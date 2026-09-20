# No `(3,3)` central top profile at `r=4,m=p=7`

Research note, 20 September 2026. This is a complete solver-free finite
incidence exclusion, not yet a Lean proof. It does not by itself exclude
the whole seven-central case.

Assume the minimum translation degree is four, the central count is
seven, and the least noncentral top-product degree is seven. The
[full-size block theorem](1485_full_central_blocks_boundary_output.md) gives
`|P_u|,|C_u|≤3` for every top. The
[uniform singleton-label separation theorem](1485_boundary_output_singleton_separation.md)
gives `S_P∩S_C=∅` analytically. The earlier finite overlap checks
remain independent corroboration, not proof dependencies here.

**Claim.** No top has both blocks of size three.

The reproducible check is

```sh
python3 -Werror scripts/1485_m7_three_by_three_check.py --audit-witnesses 100
```

## Complete normalization

Suppose a top `v` has `P_v=A`, `C_v=B`, both of size three. Choose
any central column containing `v` and any central row containing `v`.
Their respective predecessor and successor partitions each have shape
`3+2+1+1`: four nonempty blocks covering seven labels, one of size three,
and no block of size four.

Relabel the predecessor partition as

`A={0,1,2}, D={3,4}, {5}, {6}`.

In particular `5,6` are actual singleton-predecessor labels. Write the
successor partition as `B,E,{t₀},{t₁}`, where `|B|=3, |E|=2` and
`T={t₀,t₁}` consists of actual singleton-successor labels. Every global
predecessor block and successor block intersect in at most one label.
Thus `B` and `E` meet `A,D` at most once, and singleton separation
gives `T∩{5,6}=∅`.

Permutations within `A`, within `D`, and within `{5,6}` reduce the
possibilities to the following four rows. These permutations preserve
the first partition and the distinguished block `A`.

| Case | `B` | `E` | `T` |
|---|---|---|---|
| 1 | `{3,5,6}` | `{0,4}` | `{1,2}` |
| 2 | `{0,3,5}` | `{4,6}` | `{1,2}` |
| 3 | `{0,3,5}` | `{2,6}` | `{1,4}` |
| 4 | `{0,5,6}` | `{2,4}` | `{1,3}` |

For completeness: if `B` misses `A`, it must consist of one point
of `D` and both points `5,6`, giving case 1. Otherwise it contains
one point of `A`. If it also contains one point of `D`, its third
point is one of `5,6`; the other of those two points cannot lie in
`T`, so lies in `E`. The second point of `E` lies in `D` or in `A`,
giving cases 2 and 3. If `B` misses `D`, it consists of one point
of `A` and both points `5,6`; `E` contains one of the remaining
points of `A` and one of `D`, giving case 4.

## Candidate rectangles and exact covers

In each case, generate every pair `(P,C)` of nonempty subsets of seven
labels of sizes at most three. Require:

- self-orthogonality `|P∩C|≤1`;
- orthogonality to the known global blocks `A,D,B,E`;
- compatibility with the required rectangle `A×B`;
- no singleton `P` label in `T`, or singleton `C` label in `{5,6}`;
- no diagonal singleton rectangle `({x},{x})`.

For distinct candidates impose global orthogonality, disjointness of
their central rectangles, and disjointness between any actual singleton
predecessor label and any actual singleton successor label.

Also impose the precise
[boundary containment restriction](1485_boundary_singleton_overlap.md):
if `Q⊆P`, `Q∩T≠∅`, and `|C|≥2`, the two tops `(P,C),(Q,F)`
cannot coexist when `|F|≥2` or `|C|≥3`. Impose its dual using
the known actual singleton-predecessor labels `{5,6}`. Only those
known actual singleton labels are used in this filter; labels merely
allowed to be singleton are not treated as known to occur.

Search all exact covers of the 49 central cells by these rectangles,
requiring exactly four rectangles on each central row and column.
The search does **not** additionally force the chosen other blocks
`D,E,{5},{6},{t₀},{t₁}` to occur: dropping these requirements enlarges
the search and cannot invalidate a negative result. The necessary
constraints they impose are nevertheless sound, since they do occur
in any magma admitted by the normalization.

The exact-cover recursion is the previously audited `RectangleSearch`
from the [three-overlap checker](../scripts/1485_m7_overlap_three_check.py).
At each uncovered cell it branches on every compatible candidate
containing that cell. It prunes exhausted or impossible row/column
counts; no search cutoff, randomization, or external solver is used.

## Checking the necessary crowns

A completed central rectangle cover is only a necessary incidence
system, **not a magma model**. For each singleton-successor top `u`
with `C_u={c}`, and each singleton-successor omission `d` from
`Row(c)`, exact replacement requires a four-by-four crown:

- its four columns consist of the three retained tops of `Row(c)`
  and one replacement top `w` outside that row with `C_w=C_d`;
- its four row predecessor blocks partition the seven central labels,
  and one of its rows is `u`;
- the incidence entries `|C_x∩P_y|` have one zero and three ones
  in every row and every column.

All participating vertices are tops, so must be present in the completed
central rectangle cover. Test all these necessary crowns and their
predecessor/successor duals. Requiring only one witness for each crown,
independently of the others, is a relaxation of actual multiplication
and is therefore safe for an exclusion.

The witness enumerator is reused from the
[one-overlap checker](../scripts/1485_m7_overlap_one_check.py). It exhausts
replacement choices and groups the other three crown rows by their
distinct omitted retained column; their predecessor blocks must complete
a partition with `P_u`. Here its `active` mask is zero, so every witness
vertex is required to be in the completed cover. The dual enumerator
uses the same selected indices with every block pair transposed.

The program checks a positive central-incidence control and both existing
and missing crown controls. It additionally compares the first requested
number of witness calls in each case against a slower direct enumerator
using literal set-intersection counts. The controls and direct enumerator
are inherited from the already audited one-overlap implementation.

## Exhaustive result

| Case | Candidate rectangles | Search states | Completed incidence covers | Covers passing every crown |
|---|---:|---:|---:|---:|
| 1 | 419 | 72,890 | 0 | 0 |
| 2 | 501 | 337,621 | 1,870 | 0 |
| 3 | 538 | 347,821 | 5,552 | 0 |
| 4 | 501 | 378,210 | 1,870 | 0 |

The packaged run with 100 fast/direct witness audits took respectively
3.134, 12.744, 13.560, and 14.101 seconds. Every completed cover already
failed a forward crown, so the programmed dual checks were not needed
for these negative results. All four normalizations are excluded,
proving the claim. The remaining
disjoint-singleton branch can consequently assume that every size-three
predecessor block has successor block of size one or two, and dually.
