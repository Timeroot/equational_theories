# At seven central vertices, singleton predecessor and successor labels separate

Research note, 20 September 2026. This is a finite necessary-incidence
exclusion with an exhaustive, solver-free checker. It is not in Lean.
The general square/twice-square spectrum conjecture is not proved here.

Suppose a finite E1485 magma has minimum translation degree `r=4`,
central count `m=7`, and least noncentral top-product degree `p=7`.
Then

\[
\boxed{S_P\cap S_C=\varnothing.}
\]

The analytic [three-label exclusion](1485_seven_central_overlap_three.md)
and the [two-label finite check](1485_seven_central_overlap_two.md) leave
at most one common singleton label. This note excludes exactly one.
It establishes separation at central count seven; it does **not**
exclude the entire seven-central, degree-seven first-output branch.

## 1. Three complete normalizations

Suppose the unique common label is `c`. The
[boundary overlap theorem](1485_boundary_singleton_overlap.md) gives unique
tops `u,v` with

\[
(P_u,C_u)=(\{y\},\{c\}),\qquad
(P_v,C_v)=(\{c\},\{z\}),
\]

where `y∈A=S_P∖S_C` and `z∈B=S_C∖S_P`.

The six other labels may include labels belonging to neither singleton
set. Assign each such unused label to one of the two **allowed** sets
`A,B`; this only permits more singleton blocks, without requiring any
new singleton to occur. It cannot discard a genuine magma. By duality,
take the original `|A|≤|B|`, then assign all unused labels to `B`.
The only maximal allowed-set sizes needed are

`(a,b)=(1,5), (2,4), (3,3)`.

Normalize `c=0`, `A={1,...,a}`, `B={a+1,...,6}`, `y=1`,
and `z=a+1`. The two required singleton rectangles are
`({1},{0})` and `({0},{a+1})`.

## 2. Necessary central rectangles

The candidate constraints are the same as in the earlier overlap
checks, now with the single common label 0:

- Rectangles `P×C` partition all 49 central cells, with four rectangles
  on each central row and column.
- Every block has size between one and four, and every predecessor
  block meets every successor block in at most one label.
- Only labels in `A∪{0}` may be singleton predecessors, and only
  labels in `B∪{0}` may be singleton successors.
- The required singleton rectangle is unique in each orientation at 0.
- A block opposite one meeting 0 has size at most two, from the forced
  `1+2+2+2` central row and column shapes at the common label.
- Profiles `(4,1)` and `(1,4)` are forbidden by the maximal-block theorem.

These conditions leave 2,322, 2,325, and 2,326 candidate rectangles in
the three cases. Central covers satisfying these constraints do exist.
The argument therefore uses two further necessary consequences of the
first-output fiber theorem.

## 3. Two required singleton-omission crowns

Whenever `C_s={h}` and `d∈Row(h)` has singleton successor block,
exact replacement gives a degree-seven output with top profiles `U,V`
such that

\[
s\in U,\qquad
V=(Row(h)\setminus\{d\})\cup\{w\},\qquad
C_w=C_d,\quad w\notin Row(h).
\]

The predecessor blocks of `U` partition `Z`, and `|U|=|V|=4`.
The central-middle matrix `(|C_x∩P_t|)_(x∈U,t∈V)` is the crown
`J₄−I₄`, up to reordering. This is the same singleton-omission
argument used in the boundary overlap theorem; it does not require
two available omissions.

Apply it first with source `s=u`, `h=c=0`, and omitted top `d=v`.
This is the unique singleton omission from the common central row.

Apply it next with source `s=v` and `h=z=a+1`. A partition of seven
labels into four nonempty blocks has at least one singleton, so choose
a singleton-successor top `d∈Row(z)`. The checker deterministically
chooses the least-indexed one after this central row has been specified.
The theorem holds for every singleton omission, so this choice loses
no genuine magma.

These two crowns alone suffice for the exclusion. No assumption about
the remaining noncentral multiplication table is made.

## 4. Why the witness-first enumeration is exhaustive

The checker first selects `u,v` and completes `Row(0)`, branching over
every still-compatible rectangle covering a chosen uncovered cell of
that row. It then branches over every possible first crown witness.
It next completes `Row(z)`, chooses its specified singleton omission,
and branches over every possible second crown witness. It finishes
the remaining central cells using the earlier exact-cover search.

For clarity, the crown witness enumeration is elementary. Order `V`
as its three retained columns followed by replacement `w`. The row
at the singleton source has ones in the first three columns and zero
in the last. Each of the other three crown rows must hit `w` and
exactly two of the retained columns; their unique zero columns must
be 0, 1, and 2, one each. The search groups candidate rows accordingly.
It selects one from each group, checking that their predecessor blocks,
together with the source's block, partition all seven labels.
All selected rectangles must be mutually compatible.

Every actual crown has exactly this form, so it occurs in these branches.
A vertex shared by `U,V`, or already selected in the central cover, is
selected only once. The implementation uses bitsets to group candidates,
and supplies a separate direct set-intersection implementation for checks.

Selecting a witness only adds rectangles that any realization of that
witness must contain. Ordinary exact-cover pruning then deletes overlaps,
cross-intersection violations, and candidates incompatible with the four
rectangles per central line. Consequently a genuine central system with
the two necessary crowns cannot be pruned away.

## 5. Results and reproducible verification

Run [1485_m7_overlap_one_check.py](../scripts/1485_m7_overlap_one_check.py):

```sh
python3 -Werror scripts/1485_m7_overlap_one_check.py --audit-witnesses 100
```

| Allowed outside sizes | Candidate rectangles | Recursive states | Complete covers |
| --- | ---: | ---: | ---: |
| 1,5 | 2,322 | 455,715 | 0 |
| 2,4 | 2,325 | 698,286 | 0 |
| 3,3 | 2,326 | 634,463 | 0 |

The state counts and absence of covers are asserted. The audit option
compares the fast and direct witness generators on the first 100 calls
of each case. A fixed central-incidence example provides both a positive
control (its first crown exists) and a negative control (the next required
crown does not); it is explicitly not a magma model.

Initial full searches took approximately 21, 27, and 24 seconds per case.
There is no solver, timeout, omitted refutation certificate, or unproved
mathematical classification in this finite enumeration. All three
normalizations have no compatible central cover, excluding one common
label and proving singleton-label separation under the stated hypotheses.
