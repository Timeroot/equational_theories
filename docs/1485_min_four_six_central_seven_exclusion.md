# Six central vertices at minimum four exclude first-output degree seven

Research theorem, 20 September 2026. This is an analytic pen-and-paper
proof. It uses no finite enumeration or solver result and has not been
formalized in Lean.

**Theorem.** In a finite E1485 magma with minimum translation degree
four and exactly six central vertices, the least degree of a noncentral
product of two top vertices is **five or six**, not seven.

This does not exclude all magmas with these parameters, nor all magmas
of any particular order. The square/twice-square spectrum conjecture
remains open.

## 1. Boundary first outputs separate the singleton labels

Let `P_v,C_v` denote the central predecessor and successor blocks of
a top vertex. Central rows and columns partition six labels into four
nonempty blocks, so every block has size at most three and every such
partition has at least two singletons.

The [first-output bound](1485_first_top_output_fibers.md) gives
`4<p≤7`. Suppose `p=7`. Let `S_C,S_P` be the sets of labels
occurring in singleton successor and predecessor blocks respectively.
The [singleton-label theorem](1485_singleton_central_labels_first_output.md)
gives

\[
|S_C|,|S_P|\ge2,\qquad S_C\cap S_P=\varnothing.
\]

The key mechanism is exact replacement. Given `C_u={c}`, omit a
singleton-successor top from the central row at `c`. A degree-seven
first output then has four top predecessors and four top successors;
their central-middle intersection matrix is the crown `J_4-I_4`.
Every retained column has three ones, and distinct columns cannot be
comparable by inclusion of their predecessor blocks.

## 2. No three-element block can occur

Suppose first that a predecessor triple `P_v` occurs. The
[maximal-block theorem](1485_maximal_central_block_first_output_gap.md)
excludes `|C_v|=1`. Its central-column partition contains the triple
and three singleton predecessor blocks, so `|S_P|≥3`.

If `|S_C|≥3`, disjointness forces `|S_C|=|S_P|=3` and makes
them complementary. The three singleton blocks complementary to
`P_v` exhaust `S_P`, so `P_v=S_C`. The
[containment bound](1485_singleton_central_labels_first_output.md#5-containment-of-a-nonsingleton-sided-block-is-restricted)
for a top with `|C_v|≥2` and `P_v⊆S_C` gives

\[
|P_v|\le m-r=2,
\]

a contradiction. Hence a predecessor triple would require
`|S_C|=2`. But the independent
[two-singleton-label exclusion](1485_min_four_six_central_two_singleton_labels.md)
rules that out too. Its final contradiction identifies a forced crown
replacement with a diagonal central-cell top, making two blocks of
a predecessor partition overlap.

There are therefore no predecessor triples. The dual argument
excludes successor triples.

## 3. Small blocks finish the contradiction

All central blocks now have size at most two. The
[small-block first-output theorem](1485_small_central_blocks_first_output_gap.md)
gives `p≤2r−2=6`, since `r=4` and `m=6<2r`.

Concretely, another singleton omission produces a four-by-four crown
whose defining sets all have size at most two and whose row at `u`
is a singleton. The elementary
[singleton crown lemma](1485_two_set_crown_bound.md#1-a-singleton-permits-at-most-three-pairs)
forbids this. Thus `p=7` is impossible, proving the theorem.

## Proof dependencies and earlier reductions

The general finite E1485 structure, first-output fibers, maximal-block
bound, singleton-label/containment lemmas, and two-singleton-label
exclusion are the analytic dependencies. No five-neighbor incidence
classification is needed. The older
[six-central profile reductions](1485_min_four_six_central_seven_profiles.md)
and [complementary-triple exclusion](1485_min_four_six_central_disjoint_triples.md)
remain valid but their longer case splits are not dependencies of
this final proof. All new results on this page are research proofs,
not checked Lean declarations.
