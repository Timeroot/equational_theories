# Eight central labels with pair blocks: the two crown types and an incidence limitation

Research note, 20 September 2026. Assume minimum degree four,
eight central vertices, and all top central predecessor and successor
blocks of size two. This page gives a local classification and
explicit necessary-incidence examples, **not** an exclusion or an
E1485 magma construction.

Every vertex has exactly four top predecessors and four top successors:
their central blocks partition the eight central labels into pairs.
If the first noncentral top-product degree is seven, its four-by-four
central-middle matrix is therefore a crown `J₄−I₄`.

## 1. Exactly two pair-crown types occur

Let `A_i,B_i`, for `i=1,...,4`, be two-element sets with
`A_i∩B_i=∅` and `|A_i∩B_j|=1` for `i≠j`.
Up to relabeling, the complete list is:

| Type | The four `A_i`, in order | The corresponding `B_i` |
|---|---|---|
| Four-edge path | `01,12,23,34` | `24,03,14,02` |
| Two two-edge paths | `01,12,34,45` | `24,04,15,13` |

Here `01` denotes the pair `{0,1}`. Unused ground labels may
be added. In either case the opposite family has the same graph
type and is uniquely determined by the first family.

To prove completeness, view the `A_i` as four distinct edges.
The [two-set crown argument](1485_two_set_crown_bound.md#2-the-graph-of-the-first-sets)
shows that this graph is a forest of maximum degree two. Thus
its component edge counts partition four. The possibilities other
than `4` and `2+2` fail as follows:

* For `3+1`, delete the middle edge of the three-edge path.
  Avoiding its endpoints forces both leaves into the corresponding
  `B_i`, leaving no vertex to meet the isolated edge.
* For `2+1+1`, delete an edge of the two-edge path. Meeting
  its remaining edge requires the other leaf; the one remaining
  element cannot meet both isolated edges.
* Four isolated edges cannot have three remaining edges met by
  only two vertices.

Directly avoiding each edge's endpoints now forces exactly the
pairs in the table. In the two-path case, the union of the two
families is `K_{2,4}`: the two degree-two centers retain their
roles, while their two pairs of leaves are exchanged.

## 2. The global partition conditions do not exclude either type

The [standard-Python verifier](../scripts/1485_m8_pair_crown_incidence_check.py)
contains one explicit central-incidence extension of each type.
Each consists of sixteen tiles `(P_t,C_t)`, each a two-by-two
rectangle in the eight-by-eight central square, together with a
four-regular ordinary top adjacency matrix `D`. It checks:

* the sixteen rectangles partition the central square;
* the global families of predecessor pairs and successor pairs
  are edge-disjoint, so every central-middle intersection has
  size at most one;
* `BC=J`, `BD=J`, and `DC=J`, where `B,C` are the central/top
  incidence matrices;
* the four selected predecessor-profile tiles have `P` blocks
  partitioning **all eight labels**, and the selected successor-
  profile tiles have `C` blocks partitioning all eight labels;
* their `C`-versus-`P` intersection matrix is the specified crown;
* the [central-assisted top-return restrictions](1485_central_assisted_top_returns.md)
  hold for its four proposed good top pairs.

On the central and top vertices, products with a central endpoint
and top products having a central middle are determined. This is
an incomplete table with 448 specified entries out of 576. The
verifier also checks all 6,656 fully determined instances of W
and all 6,656 fully determined instances of its dual, for each
example.

```sh
python3 scripts/1485_m8_pair_crown_incidence_check.py
```

The verification takes well below one second and uses no solver.
Its data were found exploratorily; only the explicit finite checks
above are asserted here.

These examples do **not** supply the missing degree-seven output,
its three non-top neighbors, or a complete multiplication. Assigning
the four proposed good pairs a common new output imposes further
W constraints, which these incidence checks do not certify. Thus
they are not evidence that a finite E1485 magma in this branch
exists. They show precisely that the global central partitions,
the ordinary top incidence equations, and the displayed local
crown conditions alone do not yield a contradiction.
