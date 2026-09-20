# Four central and nine top vertices cannot have least noncentral degree five

Research note, 18 September 2026. This exclusion combines analytic
finite E1485 arguments with an explicit finite incidence-profile
lemma. The latter is checked by a standard-library script and is
not yet a Lean proof or a pen-and-paper classification. There is
no search over magma tables and no SAT/ATP conclusion involved.

Assume minimum translation degree three, four central vertices,
nine top vertices, and least noncentral degree five. We derive a
contradiction independently of the total order or higher degrees.

## 1. Sharp-regular degree-five vertices are impossible analytically

A least-degree-five vertex has equal sharp in/out counts `k` and
equal top-neighbor counts `t=5−k`, where `k∈{1,2,3}`.
The [two-by-two obstruction](1485_four_central_nine_top.md#5-no-sharp-regular-least-degree-five-vertices)
excludes `k=3,t=2` without computation.

Every remaining degree-five vertex has `t=3` or `t=4`. Its
central-middle matrix on its two top profiles is two-regular:
each row and column has exactly two central-valued endpoint pairs.
Indeed a top translation fiber contains its `k=5−t` sharp inputs
and `3−k=t−2` top inputs. Every other endpoint pair has a
lower-degree good replacement and is therefore centrally valued.

## 2. The explicit finite profile lemma

The executable
[`1485_m4h9_incidence_check.py`](../scripts/1485_m4h9_incidence_check.py)
with option `--degree-five` checks the following statement:

> For every allowed central-incidence diagram and every two-regular
> central-middle rectangle between top-neighborhood partitions of
> size three or four, both partitions have size three. Moreover,
> any two such rectangles in one diagram share a noncentral endpoint
> pair.

The normalization and finite search are small and explicit. The
unique `2×2` central rectangle has predecessor pair `{0,1}`;
its successor pair is either `{2,3}` or `{0,2}`, according as the
pairs are disjoint or intersect. The two horizontal dominoes occupy
central rows two and three, and the two vertical dominoes occupy
the columns outside the successor pair. Each of their four double
sets ranges over the six pairs of central labels. Overlapping
rectangles, wrong central row/column degrees, or multiple central
middles are rejected. The remaining four singleton rectangles are
then determined. These conditions leave 285 normalized diagrams.

For each diagram the script tests every three- or four-element top
subset whose predecessor labels partition the four central points,
and the corresponding successor subsets. It checks two-regularity
directly. Of the 285 diagrams, 263 have no such profile, twelve
have one, and ten have two. Every returned profile has size three
and precisely three noncentral endpoint pairs; any two profiles in
one diagram share such a pair.

The exhaustiveness comes from these explicitly bounded choices,
not from canonicalization or a solver's termination status. A
formal proof of this finite lemma remains separate work.

## 3. A singleton degree class cannot have two sharp neighbors

By the finite lemma, every degree-five vertex has `t=3` and
`k=2`. There is at most one such vertex: if distinct vertices
supplied two profiles, a shared noncentral endpoint pair would
have both as its good middle, impossible. A repeated profile gives
the same contradiction. Since degree five occurs, its entire class
is therefore a singleton `{a}`.

Every vertex of complementary degree `n/5` has a sharp predecessor
and successor of degree five. Both must be `a`. But `a` has
two distinct sharp successors, say `b_1,b_2`, and both belong to
that complementary class. Therefore both paths

\[
a\Rightarrow b_1\Rightarrow a,
\qquad
a\Rightarrow b_2\Rightarrow a
\]

are good. They have the same endpoints and different middles,
contradicting uniqueness. This completes the exclusion, with the
finite profile lemma as its sole computational premise.
