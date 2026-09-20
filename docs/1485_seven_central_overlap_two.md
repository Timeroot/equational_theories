# At seven central vertices, two common singleton labels are impossible

Research note, 20 September 2026. This is a finite necessary-incidence
exclusion with a solver-free exhaustive checker. It is not formalized in
Lean. It does not exclude the cases with zero or one common singleton label.

Suppose a finite E1485 magma has minimum degree `r=4`, central count
`m=7`, and least noncentral top-product degree `p=7`. With the notation
of the [boundary singleton-overlap theorem](1485_boundary_singleton_overlap.md),

\[
\boxed{|S_P\cap S_C|\le 1.}
\]

The boundary theorem gives an upper bound of three. The
[analytic three-common-label theorem](1485_seven_central_overlap_three.md) excludes
three. This note excludes exactly two.

## 1. The analytic reduction and the extra multiplicity condition

Write the two common labels as `0,1`. Each common label `c` has unique
singleton tops

\[
(P,C)=(\{y(c)\},\{c\}),\qquad
(P,C)=(\{c\},\{z(c)\}),
\]

where `y(c)∈A=S_P∖S_C` and `z(c)∈B=S_C∖S_P`.

The [joint-fiber lemma](1485_common_singleton_joint_fibers.md) shows that
the two outside maps cannot both be constant: two common labels sharing
both outside values would imply `7−2≤(4−2)²`, or `5≤4`.

We need one further consequence of exact replacement. There are at least
two distinct tops with successor block `{z(c)}`, and dually at least two
with predecessor block `{y(c)}`. To see the first assertion, start with
the top whose successor block is `{c}`, and omit from `Row(c)` the
unique singleton-successor top with profile `({c},{z(c)})`. Exact
replacement supplies another top with successor block `{z(c)}` outside
`Row(c)`. It differs from the omitted top. This is the same replacement
used in the boundary overlap theorem to show that `z(c)∉S_P`.

## 2. Complete normalization of the remaining cases

Some of the five labels outside `{0,1}` may belong to neither `S_P` nor
`S_C`. For the enumeration, assign each such unused label to either
`A` or `B`. This only **allows more singleton blocks**; it does not
require them to occur. Thus it enlarges the class of possible central
systems and cannot remove a genuine magma.

We may therefore assume that the two disjoint allowed outside-label sets
have sizes `a,b` with `a+b=5`.

If exactly one outside map is constant, use duality so it is `y`.
Then `a≥1`, `b≥2`. The three allocations are `(1,4)`, `(2,3)`,
and `(3,2)`. Put

`A={2,...,a+1}`, `B={a+2,...,6}`,

and normalize

`y(0)=y(1)=2`, `z(0)=a+2`, `z(1)=a+3`.

If both maps are injective, both actual outside-label sets have size
at least two. After duality and assignment of any unused label, the only
allocation needed is `(a,b)=(2,3)`. Normalize

`y(0)=2`, `y(1)=3`, `z(0)=4`, `z(1)=5`.

These four searches exhaust the possibilities. The use of duality is
legitimate for the necessary central-incidence and exact-replacement
conditions, which hold in both directions.

## 3. What is enumerated

The checker uses the same necessary rectangle conditions as the
[three-common-label regression](1485_seven_central_overlap_three.md#independent-finite-regression):

- `P×C` rectangles partition all 49 central cells, with four rectangles
  on each row and column.
- Blocks have sizes between one and four, and every predecessor block
  meets every successor block in at most one label.
- The four normalized singleton rectangles are present and are the unique
  singleton blocks of the corresponding orientation at the common labels.
- Only labels in `A∪{0,1}` may be singleton predecessors; only labels
  in `B∪{0,1}` may be singleton successors.
- A rectangle whose predecessor block meets `{0,1}` has successor
  block of size at most two, and dually. This is the forced `1+2+2+2`
  shape at a common label.
- Profiles `(4,1)` and `(1,4)` are excluded by the maximal-block theorem.

The checker imports the already described exact-cover search, retaining
all its branches and only its elementary line-count pruning. In the
both-injective case it also records the chosen rectangles, to count their
singleton labels at a completed cover. No products involving noncentral
elements, SAT solving, or unverified ATP output are involved.

## 4. Exhaustive results and the final contradiction

Run
[1485_m7_overlap_two_check.py](../scripts/1485_m7_overlap_two_check.py):

```sh
python3 -Werror scripts/1485_m7_overlap_two_check.py
```

| Outside maps | `a,b` | Candidates | Recursive states | Raw central covers |
| --- | --- | ---: | ---: | ---: |
| `y` constant, `z` injective | 1,4 | 1,221 | 729,097 | 0 |
| `y` constant, `z` injective | 2,3 | 1,223 | 754,820 | 0 |
| `y` constant, `z` injective | 3,2 | 1,223 | 800,282 | 0 |
| Both injective | 2,3 | 1,170 | 528,692 | 20 |

The first three cases already have no central covers. The twenty covers
in the fourth case all fail the analytic multiplicity condition in
Section 1. Write their singleton counts in the order

`(P at y(0), P at y(1); C at z(0), C at z(1))`.

Ten covers give `(2,2;1,2)` and the other ten give `(2,2;2,1)`.
Each therefore has an outside successor label `z(c)` that occurs as a
singleton successor block at only one top, whereas exact replacement
requires at least two. This excludes every remaining cover.

The script asserts all candidate, state, and multiplicity counts. Positive
and negative unit-grid controls check the selected-rectangle recorder as
well as the inherited exact-cover recursion. An independent rerun took
31.3, 31.1, 31.3, and 23.0 seconds for the four cases respectively.
It is an exhaustive finite
check of the stated necessary conditions, not a Lean proof. Together with
the earlier three-label exclusion, it proves the claimed upper bound one.
