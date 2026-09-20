# Dense nine-central graphs: nineteen or twenty edges with no failed rotation

Research finite graph lemma, 20 September 2026. This is a small checked
computation, not a Lean theorem. It excludes the indicated full-rotation
branches without SAT proofs or enumeration of complete magma tables.

Use `D,Q,σ,d_x,K,τ` as in the
[nonuniform bounds](1485_order_forty_nine_central_nonuniform_B.md).

**Lemma.** There is no remaining nine-central candidate satisfying

\[
                     2\le d_x\le4,\qquad
                     K\in\{19,20\},\qquad\tau=K.
\]

This lemma alone does **not** exclude the case `K=20,τ=19`.
The central-capacity arguments that reduce to these edge counts are
separate from the finite check here.

## 1. Necessary conditions and all degree profiles

If `τ=K`, every ordinary edge has its rotated edge present. Thus
the edge set is a union of whole orbits of

\[
                         \phi(x,y)=(\sigma^{-1}(y),x).
\]

Comparing row and column degrees shows that `σ` preserves the
degree classes. Since every degree is at least two, the one-`A`
five-cycle identity forbids every edge `x→σ⁻²(x)`. The proof
of both statements is given in the
[whole-orbit lemma](1485_order_forty_nine_central_sixteen_closed_orbits.md#1-with-no-failures-the-edge-set-is-a-union-of-full-orbits).
We also retain the repeated-middle bound: every entry of `D²` outside
`Q` is at most one.

Let `n_i` count vertices of degree `i`, and write `q=n_4`.
The equations `n_2+n_3+n_4=7` and `2n_2+3n_3+4n_4=K` give

\[
                         n_2=21-K+q,
                         \qquad n_3=K-14-2q.
\]

Hence `q=0,1,2` at nineteen edges, and `q=0,1,2,3` at
twenty. These seven profiles exhaust the hypotheses of the lemma.

## 2. Eighty-one canonical permutations and the complete search

Within each degree class, list one permutation of each cycle type.
This normalization is exhaustive because arbitrary relabelings within
the classes preserve all necessary conditions. The numbers of cycle
types on `1,2,…,6` points are `1,2,3,5,7,11`.

The search selects whole `φ` orbits, excluding forbidden shifts,
and prunes only excessive row/column degrees and excessive off-`Q`
entries of `D²`. It uses the previously documented first-selected-orbit
branching argument, so every allowable edge set is considered.

| `K` | `n_4` | Degree profile | Permutations | Search nodes | Intermediate graphs |
| ---: | ---: | --- | ---: | ---: | ---: |
| 19 | 0 | `(2²,3⁵)` | 14 | 3,302 | 0 |
| 19 | 1 | `(2³,3³,4)` | 9 | 3,884 | 0 |
| 19 | 2 | `(2⁴,3,4²)` | 10 | 3,959 | 0 |
| 20 | 0 | `(2,3⁶)` | 11 | 2,345 | 2 |
| 20 | 1 | `(2²,3⁴,4)` | 10 | 3,360 | 0 |
| 20 | 2 | `(2³,3²,4²)` | 12 | 4,147 | 0 |
| 20 | 3 | `(2⁴,4³)` | 15 | 4,081 | 0 |
| Total | | | 81 | 25,078 | 2 |

For nineteen edges, no graph survives even the intermediate conditions.
For twenty edges, the only two intermediate graphs share

\[
                       \sigma=(0)(1\ 2)(3\ 4\ 5\ 6).
\]

Their row bit masks, with bit `y` indicating the edge to `y`, are

```text
(6,41,81,28,50,100,74)
(6,81,41,26,52,98,76).
```

Both are independently reevaluated using literal sets. They satisfy
the degree sequences, edge-rotation equality, repeated-middle bounds,
forbidden shifts, and even the full one-`A` five-cycle implication.
However, both violate the all-`B` five-cycle identity.

For the first graph the closed walk

\[
                            6\to6\to6\to3\to2\to6
\]

has exactly one bad two-edge position, with endpoints `(6,3)`.
For the second graph, replace `2` by `1`. A two-edge position is bad
exactly when its endpoints lie in `Q`, so these explicit walks rule
out both intermediate graphs.

## 3. Controls, dependencies, and reproduction

The checker reuses the whole-orbit engine and independent set evaluator
from [1485_m9_sixteen_closed_orbits_check.py](../scripts/1485_m9_sixteen_closed_orbits_check.py).
That engine in turn reuses only two elementary cycle/partition helpers
from the adjacent fifteen-edge script. All dependencies are repository
Python files or the standard library.

The script independently traverses all 1,260 labeled degree-preserving
permutations for the seven profiles and checks that their cycle types
are included. It also uses the first surviving graph above as a positive
intermediate control. Deleting `0→1` is a negative control, rejected
by both the degree and rotation checks.

Run from the repository root:

```sh
python3 scripts/1485_m9_dense_closed_orbits_check.py
```

The expected result is

```text
PASS: 1260 normalization controls; 81 cases; 25078 search nodes; two intermediate graphs, both rejected by literal five-walks.
Elapsed: 2.722 seconds
```

The [wrapper](../scripts/1485_m9_dense_closed_orbits_check.py) asserts
the exact per-profile counts and refuses `-O` mode. Add `--verbose`
for every permutation's count. The computation is a finite necessary
graph obstruction; it is not an unrecorded SAT assertion or a claim that
the intermediate graphs extend to magma models.
