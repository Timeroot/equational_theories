# Bounded searches for non-full central cores at order 36

Research log, 18 September 2026. These searches have not produced a model
or an impossibility proof. In particular, reaching a conflict or time
limit is **unknown**, not UNSAT.

The executable is
[`1485_order36_countermodel_search.py`](../scripts/1485_order36_countermodel_search.py).
It requires `python-sat` with the `Cadical195` backend.

## Search targets

For a finite E1485 magma, write `d(x)` for its common row/column degree,
`r=min d`, and `Z` for its central class. The finite structure results give
`d(x)|n`, `max d=n/r`, and `Z={x:d(x)=r}`. We search for:

- `n=36`, `r=4`, degrees contained in `{4,6,9}`, and `|Z|≤10`;
- `n=36`, `r=3`, degrees contained in `{3,4,6,9,12}`, and `|Z|≤5`.

The [central-defect gap theorem](1485_small_central_defects.md) and its
[boundary exclusion](1485_boundary_central_defect.md) exclude every defect
from one through `r`. The [quantitative extension](1485_second_central_defect_gap.md)
also excludes defect `r+1` when `r≥4`. Thus the current caps are
10 and 5 respectively. The historical timings below predate these theorems and used
the original caps 15 and 8; they are not timings for the stronger
current encoding.

The first search also requires degree six to occur: the already proved
two-degree cardinality theorem excludes a model with exactly degrees
four and nine. Both searches require `|Z|>=r`. One way to see this lower
bound is to fix central `h`: every `t` in `Row(h)` has a central sharp
successor `z`, and then `h*z=t`, so `L_h(Z)=Row(h)`.

A discovered model would refute the general full-core conjecture, not
the proposed spectrum: 36 itself is a square. No full-core consequences
are assumed in the encoding.

## Encoding and its E1485 orientation

`P(x,y,z)` is the one-hot operation graph, `A(x,y)` the ordinary
adjacency relation, and `D(x,d)` the one-hot degree assignment. Ordinary
adjacency has both equivalent meanings:

\[
A(x,y)\iff y\in Row(x)\iff x\in Col(y).
\]

The clauses enforce both existential converses and the two implications
from each true `P(x,y,z)`: `A(x,z)` and `A(z,y)`. Each row and column of
`A` has its assigned degree. Degrees are sorted, which only removes
relabeling symmetry.

To avoid a naive five-index operation expansion, an auxiliary predicate
`G(x,a,b)` satisfies

\[
P(y,x,a)\land A(b,y)\Longrightarrow G(x,a,b),
\]
\[
G(x,a,b)\land P(x,b,c)\Longrightarrow P(a,c,x).
\]

These clauses express E1485 exactly. Indeed, `A(b,y)` says
`b=z*y` for some `z`; consequently the forced equation is
`(y*x)*(x*(z*y))=x`. Conversely, every E1485 table extends to an
assignment of `G` by taking precisely the triples forced by the first
family. The order of the adjacency arguments is important: replacing
`A(b,y)` by `A(y,b)` would encode a different identity.

The following established finite consequences strengthen propagation:

- An ordinary edge `x -> y` requires `d(x)d(y)>=36`.
- Such an edge is sharp exactly when `d(x)d(y)=36`.
- Every vertex has a sharp predecessor and successor.
- Every two-edge path containing a sharp edge is good: its middle
  vertex is the product of its endpoints.
- With `--uniform`, each left/right translation fiber has size at most
  `36/d(x)`. The exact image size and total domain size then make every
  nonempty fiber have exactly that size.

See the [finite graph results](1485_graph_research.md). The encoding does
not assume regular sharp degrees, central-rectangle closure, or any
bound `q<=2r` for three-degree models. A proposed latter bound was
withdrawn after a transpose error in its counting argument.

## Optional central normalization

With `--central-anchor`, the first central vertex is called `0` and

\[
Row(0)=\{n-r,\ldots,n-1\},
\]
\[
Col(0)=\{n-2r+1,\ldots,n-r-1\}\cup\{n-1\},
\qquad 0*0=n-1.
\]

This loses no isomorphism classes. The two sets consist of top vertices,
each has size `r`, and their intersection is the singleton `{0*0}`:
every two-step ordinary path with central endpoints is good. Relabel
the top vertices accordingly. Surjectivity `L_0(Z)=Row(0)` allows
distinct central witnesses to be labeled `1,...,r-1` so that
`0*i=n-r+i-1`. These labels are compatible with sorted degrees.

## Verification and observed limits

The built-in `--smoke-n8` pins a known eight-element model, raising the
central-count cap to its correct value four. It passes both with and
without uniform constraints, and with the central normalization. Every
SAT result is decoded and checked against all original E1485 triples;
row and column degrees and the central-count cap are also checked.

The initial runs used an external 180-second cap; the final normalized
run used 150 seconds. All four terminated at their internal conflict
budgets, with `result: null`:

| Minimum degree | Uniform fibers | Conflict budget | Solve seconds | Result |
| --- | --- | ---: | ---: | --- |
| 4 | no | 50,000 | 62.10 | unknown |
| 3 | no | 50,000 | 59.09 | unknown |
| 4 | yes | 25,000 | 66.02 | unknown |
| 4, central anchor | yes | 25,000 | 65.32 | unknown |

The uniform order-36/minimum-four instance has approximately 6.90
million clauses and 1.65 million variables. Reproduction examples:

```sh
python3 scripts/1485_order36_countermodel_search.py --smoke-n8 --uniform --central-anchor
timeout 180 python3 -u scripts/1485_order36_countermodel_search.py --minimum 4 --conflicts 50000
timeout 180 python3 -u scripts/1485_order36_countermodel_search.py --minimum 3 --conflicts 50000
timeout 150 python3 -u scripts/1485_order36_countermodel_search.py --minimum 4 --uniform --central-anchor --conflicts 25000
```

An external timeout can end a run without a final result record. That
outcome is also unknown. No proof of the full-core conjecture or any
order-36 exclusion follows from these bounded searches.
