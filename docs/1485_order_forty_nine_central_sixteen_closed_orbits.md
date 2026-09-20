# Sixteen internal edges: excluding the three leaf profiles with no failed rotation

Research graph lemma, 20 September 2026. The analytic reduction here
ends in a 24-case standard-Python check, not a Lean theorem. It is a
subcase exclusion, not by itself a proof that the entire sixteen-edge
case or the nine-central case is impossible.

**Proof-organization note.** This is now optional independent
corroboration. The [general central-capacity gap](1485_nine_central_missing_degree_five_neighbor.md#4-the-central-gap-forces-nineteen-or-twenty-internal-edges)
excludes every sixteen-edge candidate analytically, without this graph
lemma. The script's generic orbit-search engine is reused by the
[nineteen/twenty-edge checker](1485_order_forty_nine_central_dense_closed_orbits.md);
that code dependency does not make this optional sixteen-edge theorem
a mathematical premise of the main proof.

Use the notation of the
[nonuniform nine-central bounds](1485_order_forty_nine_central_nonuniform_B.md).
Thus `D` is a binary matrix on the seven degree-eight vertices, with
the same row and column degrees `d_x=7−t_x`; `Q_(x,σ(x))=1`
is their sharp endpoint permutation. An entry of `D²` outside `Q`
is at most one. The quantity `τ` counts edges with a bad successor
extension, and `K=Σd_x` counts all edges.

**Lemma.** None of the following three degree profiles can occur with
`K=τ=16`:

\[
                  (1,2^3,3^3),\qquad
                  (1,2^4,3,4),\qquad
                  (1^2,2,3^4).                         \tag{1}
\]

The proof checks necessary graph conditions, not complete magma tables.
The branch `(1,2^3,3^3), τ=14` is **not** covered by this lemma.

## 1. With no failures, the edge set is a union of full orbits

For an ordinary edge `x→y`, the bad successor indicator is
`β(x,y)=D_(y,σ(x))`. If `τ=K`, every edge has `β=1`.
The map `(x,y)↦(y,σ(x))` is a permutation of all ordered pairs.
It maps the finite edge set into itself, hence onto itself. Its inverse

\[
                         \phi(x,y)=(\sigma^{-1}(y),x)
\]

therefore also preserves the edge set. Consequently `E` is a union
of whole `φ` orbits.

The row degree of `φ(E)` at `x` is the column degree of `E`
at `σ(x)`, namely `d_(σ(x))`. Equality `φ(E)=E` gives

\[
                            d_{\sigma(x)}=d_x.           \tag{2}
\]

Thus `σ` permutes vertices separately within each degree class.

The one-`A` five-cycle identity gives the additional restriction

\[
                         D_{x,\sigma^{-2}(x)}=0
                         \quad\text{when }d_x\ge2.      \tag{3}
\]

To see this, assume `σ(u)→σ⁻¹(u)` is an edge. For every
successor `v` of `u`, closure under edge rotation gives
`v→σ(u)`. Applying the one-`A` identity to
`u→v→σ(u)→σ⁻¹(u)` forces `v=σ⁻²(u)`. This is
impossible if `d_u≥2`; equation (2) lets us relabel `x=σ(u)`.
Importantly, (3) is **not imposed at degree-one vertices**.

## 2. The complete normalization has twenty-four cases

Within each degree class, choose one representative permutation of
each cycle type. Label its cycles consecutively, with the cycle lengths
in nondecreasing order. Relabelings inside the degree classes preserve
all hypotheses, so this loses no case.

For profile `(1,2^3,3^3)`, the singleton degree class is fixed and
each of the two three-point classes has three possible cycle types:
`111,12,3`. This gives nine cases.

For `(1,2^4,3,4)`, only the four-point degree-two class varies.
Its five cycle types are `1111,112,13,22,4`.

For `(1^2,2,3^4)`, there are two cycle types on the degree-one
pair and five on the degree-three quadruple, giving ten cases.

An independent control iterates all degree-preserving labeled
permutations: `36+24+48=108` possibilities. It checks directly that
their cycle types occur in these lists.

## 3. Exhaustive whole-orbit search and independent rejection

For each of the twenty-four permutations, the checker partitions the
49 ordered pairs into `φ` orbits. Any orbit containing an edge
forbidden by (3) is discarded. The remaining orbits are either selected
whole or omitted whole.

The search chooses a row with a positive degree deficit, then branches
on the first selected available orbit meeting that row. It prunes only
when a row or column exceeds its prescribed degree, or an entry of
`D²` outside `Q` exceeds one. These failures persist under adding
edges. This is the same exhaustive first-selected-orbit argument as in
the [fifteen-edge checker](1485_order_forty_nine_central_fifteen_edges.md#3-the-complete-orbit-search-leaves-exactly-one-intermediate-graph).

The complete counts are:

| Degree profile | Permutations | Search nodes | Intermediate graphs |
| --- | ---: | ---: | ---: |
| `(1,2³,3³)` | 9 | 2,104 | 93 |
| `(1,2⁴,3,4)` | 5 | 1,922 | 42 |
| `(1²,2,3⁴)` | 10 | 1,052 | 0 |
| Total | 24 | 5,078 | 135 |

All 135 intermediate graphs are evaluated again using literal sets and
integer counts, independently of the bit-mask search. The evaluator
confirms their degree sequences, full rotation closure, repeated-middle
bound, forbidden shifts, and the full one-`A` five-cycle implication.
They all satisfy those intermediate conditions.

Every one nevertheless has a closed ordinary five-walk with exactly
one two-step endpoint pair in `Q`. This is forbidden by the all-`B`
five-cycle identity. The evaluator constructs actual five-walks directly
from its independently reconstructed neighbor sets and counts their bad
positions. Hence none of the intermediate graphs can come from a magma.

## 4. Positive and negative controls; reproduction

A fixed intermediate graph provides a positive control. It has `Q=I`
and ordinary rows

```text
0: 6
1: 2,3
2: 1,4
3: 1,5
4: 2,5,6
5: 3,4,6
6: 0,4,5
```

It meets all intermediate conditions for the first degree profile,
but `6→0→6→4→5→6` has exactly one bad position. Deleting
the edge `0→6` is a negative control: the literal evaluator must
then reject both the degree sequence and full edge-rotation closure.

Run:

```sh
python3 scripts/1485_m9_sixteen_closed_orbits_check.py
```

Observed output:

```text
PASS: 108 normalization controls; 24 cases; 5078 search nodes; 135 intermediate graphs, all rejected by literal five-walks.
Elapsed: 0.598 seconds
```

The [script](../scripts/1485_m9_sixteen_closed_orbits_check.py) uses
only the standard library and the adjacent fifteen-edge checker's two
elementary partition/permutation helpers. It can be run from any working
directory, refuses `-O` mode, and asserts all displayed case and node
counts. Add `--verbose` to print the per-permutation inventory.

This checked finite graph lemma does not address two failed rotations,
and does not assert that every sixteen-edge candidate has one of the
three profiles in (1). Those reductions or exclusions require the
separate central-capacity arguments.
