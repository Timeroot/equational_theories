# Fifteen tops: at most four smaller degree-five profiles

Independently audited finite-check component, 20 September 2026.
The full production replay passed all 69 normalized families, with
independent literal-set checks on all 226,500 complete central tables.
This note separates the mathematical reduction from the standalone
finite check. It is not a Lean proof and does not prove the full
spectrum characterization.

**Theorem.** With minimum degree four, eight central
elements, fifteen tops, and first noncentral top-output degree five,
at most four degree-five elements have three top predecessors and
three top successors. No assumption on the total number of degree-five
elements is needed. The finite lemma itself does not require order
forty; its principal application here is to that order.

Write `Z` for the eight central elements and `T` for the fifteen tops.
For a top `u`, write `P_u=Col(u)∩Z` and `C_u=Row(u)∩Z`.
Let `q` count the smaller, size-three degree-five profiles.

## 1. The exact central block inventory

Suppose `q≥5`; in this section it is enough that `q>0`.
Every central block has size at most three. The
[one-hole theorem](1485_one_hole_first_output_grid.md) bounds the
number of triple blocks in each direction by four. Since
`Σ|P|=Σ|C|=32` and there are fifteen tops, each singleton count
is two less than its corresponding triple count. In particular
there are at most two singletons in either direction.

The central rectangles partition `Z²`, so

\[
 \sum (|P|-2)(|C|-2)=64-2(32+32)+4\cdot15=-4.
\]

The left side is `n11+n33−n13−n31`. Since `n13,n31≤2`,
equality forces the following exact inventory:

| Block sizes `(|P|,|C|)` | Number of tops |
| --- | ---: |
| `(1,3)` | 2 |
| `(3,1)` | 2 |
| `(2,3)` | 2 |
| `(3,2)` | 2 |
| `(2,2)` | 7 |

There are no other types. In particular there are exactly four
maximal `P` blocks and four maximal `C` blocks. The equality case
of the one-hole theorem gives:

- Every maximal `P` block meets every maximal `C` block once.
- Each central label belongs to at most two maximal blocks of
  either kind.
- No label has multiplicity less than two in both kinds.

Repeated maximal blocks are permitted and retained in the search.

## 2. A complete normalization of the maximal blocks

Choose any one of the actual smaller profiles. Its predecessor
blocks partition `Z` into sizes `3,3,2`, as do its successor
blocks. Their intersections have size at most one. Thus they form
a three-by-three grid with exactly one missing cell, namely the
intersection of the two size-two parts. Label its occupied cells

\[
 \begin{matrix}0&1&2\\3&4&5\\6&7&\phantom{8}\end{matrix}.
\]

The first two rows are maximal `P` blocks and the first two columns
are maximal `C` blocks. Each additional maximal `P` block is a
transversal of the three columns, and each additional maximal `C`
block is a transversal of the three rows. There are eighteen choices
of either kind. Choosing two additional blocks **with repetition**
and imposing the three conditions above leaves 324 families.

To remove label duplicates, for each family take every ordered pair
of disjoint maximal `P` blocks and every ordered pair of disjoint
maximal `C` blocks. Complete each pair by its two-element complement,
relabel their occupied grid cells in the displayed order, sort the
two four-block lists, and take the least result. Such pairs always
exist, since we started with a smaller profile. Every resulting grid
has the same single missing cell: the four maximal intersections
have size one, so the two complements are disjoint.

The set of these grid presentations is invariant under every
permutation of `Z`. Hence this normalization retains a representative
of every possible maximal-block family. It leaves **69 families**.
The checker additionally tests normalization invariance on all 324
raw families under each of the seven adjacent label transpositions.

## 3. Exhausting the remaining central rectangles

For each normalized family the checker builds all possible tops:

- A fixed maximal `P` slot paired with a singleton or two-element
  `C` block, giving types `31` and `32`.
- A fixed maximal `C` slot paired with a singleton or two-element
  `P` block, giving types `13` and `23`.
- Two two-element blocks, giving type `22`.

Every proposed small block must meet every opposite maximal block
in at most one label. Two-element `P` and `C` blocks cannot be
equal, even when belonging to different tops; this is precisely
the remaining possible violation of cross-intersection at most one.

An exact-cover search selects rectangles covering each of the 64
ordered central pairs once and using each of the eight maximal
slots once. It also imposes the displayed type counts and requires
each central label to belong to four chosen blocks of each kind.
Repeated maximal slots are interchangeable: their opposite blocks
are sorted to retain one representative. These opposite blocks
must be distinct, since otherwise their rectangles would overlap.

These restrictions hold for every actual central incidence table.
The search branches on an uncovered pair or slot and tries every
remaining compatible candidate covering it. Its only pruning is
rectangle/slot conflict, the stated cross-intersection rule, the
type/valency upper bounds, and the proved repeated-slot symmetry.
Thus a completed search cannot omit an actual table.

## 4. Five actual smaller profiles would form a compatible collection

For each complete central table, enumerate every pair `(U,V)` of
three-element top sets whose `P_U` and `C_V` blocks partition `Z`.
Retain the pair if

\[
             (|C_u\cap P_v|)_{u\in U,v\in V}
\]

is a permutation matrix. By the
[first-output profile theorem](1485_first_successor_degree_profiles.md),
every actual smaller degree-five element supplies such a pair.
Its six good ordered top inputs are exactly the complement of that
permutation matrix in `U×V`.

Two distinct actual profiles must satisfy all three conditions:

1. Their good ordered inputs are disjoint, because an input pair
   has a unique product.
2. They cannot share a predecessor top with `|C|=3`: the universal
   degree-five successor capacity at such a top is one.
3. Dually they cannot share a successor top with `|P|=3`.

The capacity bound is `α≤floor(8(4−|C|)/5)`, which equals one
at `|C|=3`; it follows by summing the central-support bounds over
degree-five successors. It does not assume any particular size
of the degree-five class.

Since every retained profile has six good pairs, distinct actual
elements cannot even supply the same profile. Consequently `q≥5`
would give five distinct retained profiles satisfying these pairwise
conditions. The finite assertion is that **no complete table in any
of the 69 families has such a collection**.

## 5. Reproduction and verification boundary

Run the standalone standard-library checker from the repository root:

```sh
python3 scripts/1485_m8_fifteen_profile_check.py
```

[`1485_m8_fifteen_profile_check.py`](../scripts/1485_m8_fifteen_profile_check.py)
does not invoke SAT, an optimizer, or any other repository script.
For every complete table it independently checks central coverage,
valencies, types and cross-intersections using literal sets. A second
profile oracle scans all three-element top subsets and is compared
against the specialized partition enumerator. The absence of a
five-clique is checked both by a bitset search and by direct enumeration
of all five-profile subsets using literal good-pair sets. The fixed
production target is `FORBIDDEN_PROFILE_COUNT=5`.

Controls include a valid complete central table, a damaged table,
a positive partial profile, and positive/negative clique examples.
Both compatibility implementations additionally have explicit positive
five- and six-profile controls and negative controls for repeated good inputs,
shared capacity-one predecessors, and shared capacity-one successors.
The complete positive table must also be rediscovered by the full
search. Assertions are mandatory: `python -O` is refused. The safety
node/fixture limits cannot yield a proof, since interruption causes
an assertion failure. `--case k` checks only one named family and
its success message explicitly says so; only the default full run
can establish the finite assertion used here.

The complete target-five production replay visited **32,567,237 search
nodes and 226,500 complete central tables** in **893.285 seconds**.
All fast/literal central and profile checks agreed, every direct
five-subset test rejected, and the positive complete fixture was
rediscovered. Individual tables had up to fourteen candidate profiles;
the assertion is their incompatibility, not the absence of candidates.

An independent replay of family zero checked 2,119,263 nodes and
57,024 complete tables in 195.730 seconds for the earlier target-six
version. The complete earlier target-six replay also passed, in
876.868 seconds. The stronger target-five theorem above relies on
the separate full target-five run, not on that weaker check.
Updated size-five and size-six positive/negative controls were also
rerun independently. These are Python timings, not Lean timings.

## 6. Consequence: fifteen tops are impossible at order forty

At order forty let `a,b` count the degree-five and degree-eight
elements. Here `a+b=17`. If `q=0`, the
[all-four-profile bound](1485_order_forty_eight_central_all_four.md#1-reducing-the-top-count-and-degree-class-sizes)
already forces at least seventeen tops, not fifteen. Thus `q>0`.

The analytic [unused-top argument](1485_first_degree_source_unused_tops.md#4-at-most-two-of-the-degree-five-profiles-are-large)
gives `a−q≤2`; the finite theorem gives `q≤4`. Sharp-neighbor
coverage gives `b≤a+q`. Consequently

\[
                  17=a+b\le2a+q\le3q+4\le16,
\]

a contradiction. This excludes **every fifteen-top case at order forty
with eight central elements**, not merely the previously extreme class
size ten. The latter also has a separate purely analytic exclusion.
