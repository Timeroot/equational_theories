# Historical incidence leads for the five-central exclusion

Research log, 18 September 2026. This is a reproducible finite incidence
filter, **not a search through magma tables, a Lean proof, or a new
impossibility theorem**. The pen-and-paper reductions are in the
[nine-top note](1485_five_central_nine_top.md).

**Subsequent resolution:** the [binary-type proof](1485_five_central_binary_blocks.md)
now excludes the entire five-central case analytically. It proves the
common binary matrix structure without this enumeration and then uses
finite degree bounds to contradict it. The scan remains reproducible
research history; none of its counts is a premise of that proof.

The executable is
[`1485_m5h9_packing_scan.py`](../scripts/1485_m5h9_packing_scan.py)
and uses only the Python standard library.

## What is imposed

Start with five central points and nine top vertices of profiles
`1(1,1), 2(1,2), 2(2,1), 4(2,2)`. Each top vertex is specified
by its central predecessor set `P_t` and successor set `C_t`.
The rectangles `P_t×C_t` must partition all twenty-five central
pairs, every central row and column has degree three, and
`|C_t∩P_u|≤1`.

For each incidence diagram the script asks whether some ordinary
top adjacency `D` exists with row and column sums three,
`BD=DC=J`, and the size-two witness equality from E1485 in both
directions. Three-regularity follows analytically: the packing bound
gives each top vertex at least three top successors and predecessors,
and summing those counts in `BD=DC=J` forces equality.

The unique `(1,1)` vertex has central labels `p,q`. The other
weight-one profiles give two partitions into pairs. Their intersections
have size at most one. Up to relabeling, this gives two starting
alignments: `p=q` or `p≠q`. The remaining four two-by-two rectangles
are filled by exact cover. Returned diagrams and `D` witnesses are
checked directly against the stated constraints.

## Observed output

The two normalized alignments produce 591 and 495 incidence diagrams.
Seven admit a `D` passing the filter, all in the `p=q` alignment.
They form three orbits under central relabeling, duality, and unordered
top labels. These are incidence orbits, **not a classification of all
possible `D` matrices**.

Here are convenient representatives. Strings such as `12` denote
subsets `{1,2}` of the five central points. All three have

```text
P = [0, 0, 0, 12, 34, 12, 12, 34, 34]
```

Their successor lists are:

| Candidate | Central successor sets `C` |
| --- | --- |
| A | `[0, 13, 24, 0, 0, 13, 24, 13, 24]` |
| B | `[0, 13, 24, 0, 0, 13, 24, 14, 23]` |
| C | `[0, 13, 24, 0, 0, 14, 23, 14, 23]` |

One compatible ordinary top adjacency, common to all three, has rows

```text
D = [012, 356, 478, 012, 012, 356, 478, 356, 478].
```

Their central row/column-sharing components have sizes `(1,4)` for
A and `(1,2,2)` for B and C. Thus the
[connected-parameter criterion](1485_central_parameter_components.md)
does not eliminate these witnesses.

No multiplication on the noncentral outputs was constructed. These
incidence survivors are now ruled out by the analytic proof linked
above. The observed enumeration counts remain separate from that proof.
