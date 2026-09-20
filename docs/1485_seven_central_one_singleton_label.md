# At seven central vertices, both singleton-label sets have at least two labels

Research note, 20 September 2026. This is a finite necessary-incidence
exclusion, with a solver-free exhaustive checker. It is not in Lean and
does not settle the square/twice-square spectrum conjecture.

Suppose a finite E1485 magma has minimum translation degree `r=4`,
central count `m=7`, and least noncentral top-product degree `p=7`.
Write `S_C,S_P` for its singleton successor and predecessor labels.
Then

\[
\boxed{|S_C|\ge2,\qquad |S_P|\ge2.}
\]

Together with [singleton-label separation](1485_seven_central_overlap_one.md),
the remaining case therefore has two disjoint singleton-label sets,
each of size at least two. That remaining case is **not excluded here**.

## 1. Only three normalizations

Every central row partitions seven labels into four nonempty successor
blocks, so `S_C` is nonempty. Suppose it is the singleton `{c}`.
The [single-label graph reduction](1485_single_successor_label_graph.md)
shows that every successor block is `{c}` or a pair avoiding `c`.
There are exactly four tops with block `{c}` and twelve with pair
blocks. The predecessor blocks of the first four tops partition all
seven central labels.

The [boundary maximal-block exclusion](1485_boundary_singleton_overlap.md)
makes every predecessor block have size at most three. By separation,
`c∉S_P`, so the predecessor block of the unique `{c}`-successor top
containing `c` is not singleton. Call this top `d`.

Consequently the four `{c}`-successor tops have predecessor-block sizes,
with `d` first,

\[
(3,2,1,1),\qquad(2,3,1,1),\qquad(2,2,2,1).
\]

Set `c=0`. Relabeling within these blocks gives the following complete
normalizations of their predecessor partitions:

| Shape | Predecessor blocks, with the diagonal block first |
| --- | --- |
| 3211 | `{0,1,2}`, `{3,4}`, `{5}`, `{6}` |
| 2311 | `{0,1}`, `{2,3,4}`, `{5}`, `{6}` |
| 2221 | `{0,1}`, `{2,3}`, `{4,5}`, `{6}` |

These are disjoint-block normalizations, not assumptions that unrelated
central labels or tops are equivalent.

## 2. The necessary finite incidence conditions

For each top `v`, its nonempty central blocks `P_v,C_v` obey:

- The rectangles `P_v×C_v` partition the 49 central cells.
- Every central row and column meets exactly four rectangles.
- `|P_v|≤3`; no predecessor block is `{0}`.
- Every successor block is `{0}` or a pair in `{1,...,6}`.
- Every predecessor block meets every successor block in at most one label.
- The four `{0}`-successor rectangles are exactly the normalized ones above.

There are 844 candidate rectangles in each normalization. The checker
uses the same elementary exact-cover engine as the earlier
[three-overlap check](1485_seven_central_overlap_three.md).

These incidence conditions alone are insufficient. Even all replacement
crowns in the forward orientation are insufficient: the checker includes
an explicit incidence cover satisfying all forward crowns but failing a
dual crown as a control. This cover is not asserted to be a magma.

## 3. The additional crown conditions

Whenever `C_u={h}` and `d∈Row(h)` has singleton successor block,
the finite exact-replacement theorem supplies top profiles `U,V` with

\[
u\in U,\qquad
V=(Row(h)\setminus\{d\})\cup\{w\},\qquad
C_w=C_d,\quad w\notin Row(h).
\]

Their sizes are four. The predecessor blocks of `U` partition `Z`,
and the matrix `(|C_x∩P_y|)_(x∈U,y∈V)` is `J₄−I₄`, up to
reordering. The dual condition is equally necessary.

The search first completes `Row(0)` and selects the crown with source
and omitted top both equal to the distinguished diagonal top `d`.
This choice is allowed: `C_d={0}` and `d∈Row(0)`. It then completes
the remaining central cover and tests **every** singleton-source,
singleton-omission crown in **both** orientations.

To enumerate the first crown, order its columns as the three retained
tops followed by the replacement. The source row is `1110`. Each
other row meets the replacement and exactly two retained columns;
their missing columns must be the three different retained columns.
The checker groups the candidates by this missing column and selects
one from each group whose predecessor blocks, together with `P_d`,
partition all seven labels. This enumerates every possible first crown.

A rectangle already chosen is not chosen a second time when it also
appears in the crown. Every added rectangle is checked for ordinary
exact-cover compatibility. Thus a genuine central system with its
required crowns appears in the search; no part of its multiplication
table is presumed beyond these proved necessary conditions.

## 4. Reproducible check and controls

Run [1485_m7_one_singleton_label_check.py](../scripts/1485_m7_one_singleton_label_check.py):

```sh
python3 -Werror scripts/1485_m7_one_singleton_label_check.py --audit-witnesses 100
```

The code compares the first 100 partial-cover witness calls in each case
with a separate direct implementation. On the fixed incidence control,
it also compares the complete-cover crown test with both witness
implementations for every applicable source and omission, in both
orientations. The control passes all forward crowns and fails the dual
test, so the two orientations are not accidentally conflated.

All three normalizations have no cover satisfying the necessary crowns.
The exhaustive search has no solver dependency, timeout, omitted
refutation certificate, or unproved mathematical classification. It
excludes `|S_C|=1`; duality excludes `|S_P|=1`.

The packaged checker, including 100 witness audits per case, gives:

| Shape | Recursive states | First-crown choices | Raw cover visits | Total time |
| --- | ---: | ---: | ---: | ---: |
| 3211 | 338,182 | 27,104 | 59,176 | 15.6 s |
| 2311 | 629,971 | 65,340 | 108,024 | 29.2 s |
| 2221 | 407,493 | 56,128 | 61,504 | 20.1 s |

All three counts per case are asserted in the checker. Complete-cover
visits can repeat the same cover under different first-crown witnesses;
they are not counts of distinct isomorphism classes.
