# At seven central vertices, a triple cannot be opposite a singleton

Research note, 20 September 2026. This is a solver-free finite
necessary-incidence exclusion, not a Lean proof or a full spectrum
classification.

Suppose a finite E1485 magma has minimum translation degree `r=4`,
central count `m=7`, and least noncentral top-product degree `p=7`.
Then no top has central-block profile `(3,1)` or `(1,3)`.

The proof uses the established [exclusion of `(3,3)`](1485_seven_central_three_by_three.md),
but does **not** exclude or assume the absence of `(3,2)` or `(2,3)`.
The remaining possible triple-block tops have exactly those latter
two profiles. This distinction prevents a circular use of the result.

## 1. Two complete normalizations

Suppose a top `u` has `|P_u|=3` and `C_u={z}`. The predecessor
blocks of the four tops in `Col(z)` partition seven labels. Since
one is a triple, the other sizes are two, one, and one.
Normalize this actual partition as

\[
A=\{0,1,2\},\qquad D=\{3,4\},\qquad\{5\},\qquad\{6\},
\qquad P_u=A.
\]

The labels 5 and 6 genuinely belong to `S_P`, whereas `z∈S_C`.
[Analytic singleton-label separation](1485_boundary_output_singleton_separation.md) therefore
puts `z` in `A` or `D`. Permuting within these blocks leaves only
two cases:

\[
\boxed{z=0\quad\text{or}\quad z=3.}
\]

This is a normalization of the chosen central-column partition, not
an assertion that the singleton-label sets consist only of the labels
just specified.

## 2. Necessary rectangle constraints

The checker enumerates top rectangles `P×C` covering the central
7-by-7 grid, with exactly four rectangles through every row and column.
It uses these additional proved constraints:

- All blocks have size at most three, by the
  [full-size block exclusion](1485_full_central_blocks_boundary_output.md).
- No profile is `(3,3)`, by the earlier finite check.
- Every predecessor/successor intersection has size at most one.
  In particular every global successor block meets each of `A,D`
  in at most one label, since both are actual predecessor blocks.
- No singleton predecessor is `{z}` and no singleton successor is
  `{5}` or `{6}`.
- Every rectangle whose successor block contains `z` has predecessor
  block exactly one of `A,D,{5},{6}`. This is the prescribed actual
  partition of `Col(z)`.
- The distinguished rectangle `(A,{z})` is required.

The checker also imposes singleton separation between selected
rectangles and the [boundary containment restrictions](1485_boundary_singleton_overlap.md).
For distinct rectangles `(P,C),(Q,F)`, it discards the pair when

\[
Q\subseteq P,\quad z\in Q,\quad |C|\ge2,
\quad (|F|\ge2\text{ or }|C|\ge3),
\]

or when its dual holds using either known singleton predecessor
label 5 or 6. Both orders of the pair are checked. These are
necessary incompatibilities; no information about unknown singleton
labels is invented.

The candidate pools have 1,295 rectangles for `z=0` and 1,200 for
`z=3`. They deliberately permit `(3,2)`, `(2,3)`, and `(1,3)`.

## 3. One crown first, then all crowns

Complete the central row at `z`. Its successor blocks form a
four-block partition of seven labels and therefore include a singleton.
Choose the least-indexed singleton-block top `d` in that completed
row. The exact-replacement theorem applies to source `u`, omission
`d`, and its new top `w`:

\[
u\in U,\qquad
V=(Row(z)\setminus\{d\})\cup\{w\},\qquad
C_w=C_d,\quad w\notin Row(z).
\]

The profiles `U,V` have size four, the `P` blocks of `U` partition
`Z`, and their central-middle matrix is the crown `J₄−I₄`.
The theorem holds for every singleton omission, so choosing one
deterministically does not discard a genuine model.

The checker enumerates every such first crown by its replacement and
the unique missing retained column of each of its other three rows.
It then completes the central cover and checks every singleton-source,
singleton-omission crown in both orientations. The exhaustive branching
and compatibility argument is the same as in the
[single-label check](1485_seven_central_one_singleton_label.md).

## 4. Reproducible finite exclusion

Run [1485_m7_three_by_one_check.py](../scripts/1485_m7_three_by_one_check.py):

```sh
python3 -Werror scripts/1485_m7_three_by_one_check.py --audit-witnesses 100
```

The checker compares fast and direct crown enumeration on the first
100 partial-cover calls and on up to 100 complete-cover calls in each
case. Its shared controls include both an existing crown and a missing
crown on an independently valid incidence cover.

| Singleton label | Candidates | Recursive states | First-crown choices | Raw cover visits | Total time |
| --- | ---: | ---: | ---: | ---: | ---: |
| In `A` (`z=0`) | 1,295 | 1,116,058 | 808,021 | 9,504 | 44.7 s |
| In `D` (`z=3`) | 1,200 | 339,202 | 108,771 | 0 | 24.4 s |

All counts are asserted. Every raw cover in the first case fails a
forward crown; the second case has no cover after its first crown
is imposed. Raw cover visits may repeat a cover under different crown
choices. The reported total times include the witness audits.

Thus no `(3,1)` top exists. Duality excludes `(1,3)`. No external
solver, timeout, missing certificate, or unproved classification is
used in the finite enumeration.

## 5. A small consequence for the surviving triple profiles

With `(3,3)`, `(3,1)`, and `(1,3)` excluded, every successor triple
belongs to a top with exactly two central predecessors. Every central
row has at most one triple block. Therefore, if `N23` counts `(2,3)`
tops, exactly `2N23` central rows contain a triple, giving `N23≤3`.
Dually `N32≤3`. In either orientation at least one central partition
has shape `2+2+2+1`. These are restrictions on the remaining cases,
not an exclusion of `(3,2)` or `(2,3)`.
