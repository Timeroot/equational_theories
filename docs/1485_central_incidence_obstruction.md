# Central and top incidence alone does not force r-squared top vertices

Research note, 18 September 2026. This is a counterexample to a
**combinatorial intermediate claim**, not an E1485 magma and not a
counterexample to the spectrum conjecture.

Let `B` be central-to-top incidence and `C` top-to-central incidence.
The elementary necessary conditions include

\[
 B\mathbf1=r\mathbf1,\qquad
 \mathbf1^TC=r\mathbf1^T,\qquad
 BC=J_m,\qquad CB\le J_h.                         \tag{1}
\]

Every top column of `B` and top row of `C` is nonempty and has at
most `r` entries. If `D` denotes ordinary top-to-top adjacency,
central-endpoint goodness additionally gives

\[
 BD=J_{m,h},\qquad DC=J_{h,m}.                    \tag{2}
\]

Even (1)--(2) together do **not** imply `h≥r²`.

## A twelve-vertex incidence diagram

Take `m=4`, `r=3`, and `h=8`. Label the central vertices
`0,1,2,3`, and the top vertices `0,...,7`. The central predecessor
and successor sets of each top vertex are as follows.

| Top vertex `t` | `P_t={i:B_it=1}` | `Q_t={j:C_tj=1}` |
|---|---|---|
| 0 | `{0,3}` | `{0}` |
| 1 | `{0}` | `{1,3}` |
| 2 | `{0,3}` | `{2}` |
| 3 | `{1}` | `{0,2}` |
| 4 | `{2}` | `{0,2}` |
| 5 | `{1,2}` | `{3}` |
| 6 | `{1,2}` | `{1}` |
| 7 | `{3}` | `{1,3}` |

The eight rectangles `P_t×Q_t` each have area two and partition
the sixteen ordered central pairs. Every central vertex belongs to
exactly three `P_t` and exactly three `Q_t`. The only two-element
`P_t` sets are `{0,3}` and `{1,2}`; the only two-element `Q_t`
sets are `{1,3}` and `{0,2}`. Thus `|Q_t∩P_u|≤1` for all
`t,u`. This verifies (1) directly, including the profile bounds.

Here is a compatible zero-one matrix `D`, specified by its row
supports:

```text
0: 0 2 7
1: 1 3
2: 4 5 6
3: 4 7
4: 4 7
5: 0 1 2
6: 3 5 6
7: 1 3
```

For each row of `D`, the corresponding `Q_t` sets partition the
central set; for each column, the corresponding `P_t` sets do so.
This verifies (2). In particular, with `K=CB`, it also gives

\[
 DK=\mathbf1(\mathbf1^TB),\qquad
 KD=(C\mathbf1)\mathbf1^T.                       \tag{3}
\]

The top out-degrees and in-degrees of `D` are respectively

```text
out: 3 2 3 2 2 3 3 2
 in: 2 3 2 3 3 2 2 3
```

They are all at most `r`. Moreover, after adding each top vertex's
central successors or predecessors, every top vertex has degree four
in both directions inside the displayed central/top diagram.

Thus unweighted in/out degree balance on the induced diagram does
not remove the example. Weighted reciprocal-degree balance in an
actual larger magma would require suitable additional neighbors;
none are constructed here.

## Scope of the obstruction

The data were found by a small Boolean constraint search, but every
claimed property above is checked directly from the displayed sets.
There is no operation table on these twelve vertices. In particular,
the labels “central” and “top” specify the intended incidence roles,
not properties proved for an E1485 multiplication.

Kronecker powers of the matrices preserve (1)--(2) and the positive
profile bounds. They have

\[
 m=4^k,\qquad r=3^k,\qquad h=8^k<9^k=r^2.
\]

Consequently no inequality `h≥r²` can follow solely from those
matrix identities, even asymptotically. This does not assert that
the additional unweighted core-degree balance of the base diagram
is preserved by Kronecker powers.

A proof for finite E1485 magmas must therefore use further
information, such as the degrees and fibers of the noncentral
products of top vertices or additional five-cycle consequences.
