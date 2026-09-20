# The nine-central remainder cannot have fifteen internal edges

Research theorem, 20 September 2026. This excludes one subcase of the
remaining order-forty problem. Its analytic reduction ends in a tiny
standard-Python graph check: ninety normalized cases and seventy-nine
search nodes. It does not enumerate magma tables and uses no SAT solver.
The proof and implementation have been independently audited and rerun by
the main research agent. It is not yet a Lean theorem.

The [nonuniform bounds](1485_order_forty_nine_central_nonuniform_B.md)
use the notation `B,D,Q,σ,K` from the nine-central reduction. This
note proves **`K≠15`**, leaving `16≤K≤20` unless further cases
are excluded separately.

**Proof-organization note.** The subsequent
[general central-capacity gap](1485_nine_central_missing_degree_five_neighbor.md#4-the-central-gap-forces-nineteen-or-twenty-internal-edges)
now excludes `K=15` analytically as well. The present tiny graph lemma
is retained as independent corroboration, not a required mathematical
premise of the shortest nine-central proof.

## 1. The analytic reduction to one partially occupied orbit

If `K=15`, the existing exact top-pair budget and the one-top-product
gap give:

- `D` has row and column degrees `(3,2,2,2,2,2,2)`;
- there are no top-valued products of two tops;
- exactly fourteen internal edges have a bad successor extension,
  and exactly fourteen have a bad predecessor extension;
- if `h` is the unique degree-three vertex, then `σ(h)≠h`;
- for some `a`, the unique failed predecessor edge is `(a,h)`,
  and the unique failed successor edge is `(h,a)`;
- `D_(x,σ⁻²(x))=0` for every vertex `x`.

The last fact uses the one-`A` five-cycle identity and the fact that
every vertex has at least two outgoing edges with a bad successor
extension. All these statements are proved in the linked note; none is
inferred from the computation below.

Let `E` be the set of edges and put

\[
 \phi(x,y)=(\sigma^{-1}(y),x),\qquad
 f=(h,a),\qquad e=(a,h).
\]

The exact failure counts say

\[
 E\setminus\phi(E)=\{f\},\qquad
 \phi(E)\setminus E=\{\phi(e)\}.                       \tag{1}
\]

On each cyclic orbit of the permutation `φ`, an occupied proper
subset has as many entrances as exits. Equation (1) therefore forces
exactly one partially occupied orbit. Its occupied portion is the
consecutive segment

\[
                         f,\phi(f),\ldots,e.            \tag{2}
\]

In particular `e` must be on the orbit of `f`, and `φ(e)` must
not occur in this segment. Every other `φ` orbit is either wholly
included or wholly excluded. The segment is allowed to have one edge,
when `a=h`.

This gives a particularly small exhaustive construction of every
remaining graph. The checker never guesses arbitrary individual edges.

## 2. Why the ninety normalizations are complete

Relabel the distinguished vertex `h` as zero. Its `σ` cycle has
length `l≥2`; label that cycle successively `0,1,…,l−1`.
List all remaining cycle lengths in nondecreasing order, and label each
cycle consecutively. This accounts for nineteen distinguished cycle
types. A further relabeling commuting with `σ` can rotate any of its
other cycles and interchange cycles of equal length.

Consequently, the representative `a` may be:

- any one of the `l` positions on the distinguished cycle;
- the first point of one chosen cycle of each distinct remaining length.

These are exactly the following ninety cases:

| Distinguished cycle length | Remaining cycle lengths | Choices for `a` |
| --- | --- | ---: |
| 2 | 1,1,1,1,1 | 3 |
| 2 | 1,1,1,2 | 4 |
| 2 | 1,1,3 | 4 |
| 2 | 1,2,2 | 4 |
| 2 | 1,4 | 4 |
| 2 | 2,3 | 4 |
| 2 | 5 | 3 |
| 3 | 1,1,1,1 | 4 |
| 3 | 1,1,2 | 5 |
| 3 | 1,3 | 5 |
| 3 | 2,2 | 4 |
| 3 | 4 | 4 |
| 4 | 1,1,1 | 5 |
| 4 | 1,2 | 6 |
| 4 | 3 | 5 |
| 5 | 1,1 | 6 |
| 5 | 2 | 6 |
| 6 | 1 | 7 |
| 7 | none | 7 |

As a separate control, the script traverses all 4,320 labeled
permutations moving zero, for each of the seven choices of `a`.
It constructs an explicit relabeling and confirms that the resulting
pair belongs to this list: 30,240 normalization checks. The mathematical
coverage argument above does not rely on this control.

## 3. The complete orbit search leaves exactly one intermediate graph

For each normalized pair `(σ,a)`, the checker constructs segment
(2). It rejects a case if the segment does not terminate properly, or
contains an edge `x→σ⁻²(x)`. It partitions the remaining ordered
pairs into full `φ` orbits, discarding any orbit containing such a
forbidden edge.

It then chooses which of those orbits to include. After each addition
it rejects a partial graph if:

- a row or column exceeds its prescribed degree;
- some entry of `D²` outside `Q` exceeds one.

Both tests are monotone under adding edges, so these prunings cannot
discard a solution. To search exhaustively without duplication, choose
a row with a positive degree deficit and order all available orbits
meeting it. Every extension has a first selected orbit in that order;
branch on this first choice, excluding the preceding choices. Recursion
continues until every row and column has its prescribed degree.

The entire search visits seventy-nine recursion nodes. Exactly one
complete graph survives:

\[
 \sigma(x)=x+1\pmod7,\qquad
 E=\{(x,x-1),(x,x+2):x\in\mathbf Z/7\}\cup\{(0,0)\}.
\tag{3}
\]

The script evaluates this graph a second time using literal sets and
integer counts, independently of its orbit constructor and bit-mask
pruning. It checks the two degree sequences, repeated-middle condition,
unique failed rotations, forbidden shift, and the full one-`A`
five-cycle implication. All of those conditions hold: (3) is a positive
control for the intermediate system, not a magma model.

## 4. An explicit forbidden five-walk kills the last graph

In the all-`B` five-cycle identity, a two-edge position is bad exactly
when its endpoints lie in `Q`. Indeed the only possible smaller middle
between two `B` endpoints is the unique sharp `A` middle; central
vertices have only top neighbors. A closed ordinary five-walk cannot
have exactly one bad position.

Graph (3) has the closed walk

\[
                         0\to0\to2\to1\to0\to0.
\]

Among its five two-edge positions, only the position with endpoints
`(0,1)` lies in `Q`. The other endpoint pairs are `(0,2)`,
`(2,0)`, `(1,0)`, and `(0,0)`. This contradicts the five-cycle
identity, excluding the final graph and therefore `K=15`.

The literal evaluator also loops through all `7^5` vertex sequences,
independently finding the displayed violation. No statement that every
closed walk has distinct vertices is used; repetitions and loops are
essential in this last obstruction.

## 5. Reproduction and scope

Run from the repository root:

```sh
python3 scripts/1485_m9_fifteen_edges_check.py
```

Observed output:

```text
PASS: 30240 normalization controls; 90 cases; 79 search nodes; one intermediate graph, rejected by a literal five-walk.
Elapsed: 0.761 seconds
```

Add `--verbose` for all ninety per-case counts. The standard-library
script is [1485_m9_fifteen_edges_check.py](../scripts/1485_m9_fifteen_edges_check.py).
Deleting the loop from the positive intermediate fixture provides a
negative control: the independent evaluator must reject both its degree
sequence and its unique-failure condition. The script refuses Python's
`-O` mode rather than silently running with assertions disabled.
This is a transparent finite computation with independent controls,
not a Lean proof or a proof certificate checked by Lean. The other
nonuniform edge counts and the full spectrum conjecture are not settled
by this result.
