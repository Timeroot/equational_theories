# Order forty: thirteen degree-five vertices cannot have one high-sharp partner

Research note, 19 September 2026. This is a **finite-assisted
exclusion** of the sharp-degree distribution `(1,1,2,2,2,2,3)`
in the thirteen/seven branch at order forty. It uses precisely the
analytic incidence conditions proved in the
[two-high-sharp note](1485_order_forty_thirteen_two_high.md), followed
by a complete standard-Python enumeration of two seven-point binary
matrices. It uses no SAT solver or unpublished certificate and is
not yet a Lean theorem.

Together with the analytic exclusion of three high-sharp partners
and the finite-assisted exclusion of two, this forces any remaining
thirteen/seven model to have sharp degrees

\[
\boxed{(1,2,2,2,2,2,2).}
\]

That last distribution is now excluded by the
[final incidence reduction and analytic profile obstruction](1485_order_forty_thirteen_directions.md).
Together these arguments exclude the entire thirteen/seven branch,
but not every order-forty model. This page supplies only its
one-high-sharp component.

## The same exact incidence check, with different margins

The two binary matrices are ordinary internal adjacency `D` and
sharp two-step adjacency `C`. For the present ordered sharp vector
`j=(1,1,2,2,2,2,3)`, their row and column sums are respectively
`4−j` and `j`. The checker imposes the same four conditions as in
the two-high-sharp note:

1. Forced `C` entries from multiple internal middles and the
   degree-sensitive return-matching bound.
2. Edgewise equality of bad extensions and bad predecessors.
3. Five-walk closure when the closing middle has degree five.
4. The bound on all-`B` good-good three-paths for each return,
   using fiber size eight, five or four according to its output class.

The proofs of these conditions do not assume the particular sharp
vector, so no new mathematical premise is needed.

Run the explicitly separate mode

```sh
python3 scripts/1485_n40_thirteen_two_high_check.py --one-high
```

The [shared checker](../scripts/1485_n40_thirteen_two_high_check.py)
derives the row margins and relabeling classes from this sharp vector.
It asserts its own full set of exact counts:

| Stage | Number remaining |
| --- | ---: |
| Internal matrices `D` with the prescribed margins | 1,413,400 |
| Internal matrices whose forced `C` entries fit the margins | 27,984 |
| Completed pairs `(D,C)` | 1,547,520 |
| After edgewise bad-extension balance | 3,024 |
| After one-`A` five-walk closure | 312 |
| After the return-path budgets | **0** |

The last 312 pairs have seven types up to sharp-degree-preserving
relabeling: six with 48 labelings and one with 24. The program checks
every labeled pair, then prints a canonical representative and an
explicit forbidden return-path collection for each type. This
classification is explanatory, not an assumption in the exhaustive
check.

Six canonical types are already contradicted by a top-valued return.
The seventh genuinely uses the strengthened theorem for a
degree-eight return: its sharp-degree-three vertex `6` and
sharp-degree-two vertex `2` have a degree-eight product, whose
return fiber has size five. Their five sharp neighbors fill that
matching, leaving zero capacity for the good-good all-`B` path

\[
2\longrightarrow3\longrightarrow1\longrightarrow6.
\]

The checker exhibits this path explicitly. Thus the extension from
top-only return matching to arbitrary returns has a concrete role
in this exclusion.

The published `--one-high` run took approximately **147 seconds**
in this workspace (an initial independent parameterized run took
158 seconds). No multiplication table is constructed or asserted
to exist at any intermediate stage.
