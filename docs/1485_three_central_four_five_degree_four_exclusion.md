# Four degree-four vertices are impossible; an independent five-vertex check

Research note, 19 September 2026. The four-vertex exclusion below is
a finite E1485 proof assisted by an explicit profile enumeration,
not SAT, an ATP, or a search over magma tables. The executable also
provides an independent finite check for the five-vertex case. No
Lean theorem is asserted.

**Theorem.** A finite E1485 magma with minimum translation degree
three and exactly three central vertices cannot have exactly four
degree-four vertices.

All analytic ingredients are the same as in the
[three-degree-four-vertex exclusion](1485_three_central_three_degree_four_exclusion.md).
We spell out the additional sharp-fiber restrictions and the
normalization of the finite enumeration.

## 1. Necessary profile and sharp-map conditions

Let `A` be the degree-four class, `B` its reciprocal degree class,
and `F,G:A→B` its sharp successor and predecessor maps. Every
vertex has three top neighbors in each direction. The profiles
`U_a=TopPred(a)` and `V_a=TopSucc(a)` for `a∈A` are permutation
transversals of the nine-top grid. There are 36 possible pairs of
such transversals, with pairwise distinct six-element good sets.
Actual degree-four vertices have disjoint good sets.

The maps `F,G` are onto, `(F,G)` is injective, and

\[
\begin{aligned}
F(a)=F(c),\ a\ne c&\Longrightarrow U_a\cap U_c=\varnothing,\\
G(a)=G(c),\ a\ne c&\Longrightarrow V_a\cap V_c=\varnothing. \tag{1}
\end{aligned}
\]

For example, a common top predecessor of `a,c` in the first line
would give two good middles on paths ending at their common sharp
successor. The second line is dual. Also,

\[
F(a)\ne G(c)\Longrightarrow |V_a\cap U_c|=1.       \tag{2}
\]

The [mixed-product argument](1485_three_central_three_degree_four_exclusion.md#2-sharp-maps-and-mixed-degree-fourdegree-five-products)
gives the following filter on every degree-five candidate with top
profiles `U,V`:

\[
\begin{aligned}
\left|\{F(a):|V_a\cap U|\ne1\}\right|&\le1,\\
\left|\{G(a):|U_a\cap V|\ne1\}\right|&\le1.        \tag{3}
\end{aligned}
\]

Its other necessary conditions remain unchanged: its good set is
`(U×V)\(K∪G_A)`, each row and column has one or two entries,
the total is at most four, and every position in a two-entry good
row or column has a degree-four companion. Every central-column
triple and its dual must have a degree-four or degree-five output.

## 2. Enumeration without an implicit symmetry assumption

The command is

```text
python3 scripts/1485_m3_sharp_fiber_check.py --size 4
```

It starts with all 4,140 disjoint four-element collections of the
36 degree-four profiles. No central or top relabeling quotient is
used. Taking the union of all preliminary degree-five candidate
good sets and testing the mandatory low-output triples leaves
648 collections.

For each collection, enumerate all onto maps `F,G` to a labeled
set of size `2,3,4`, subject to joint injectivity and (1)–(2).
The only normalization is simultaneous relabeling of that codomain.
In the fixed order of the four profile vertices, labels of `F`
must appear for the first time as `0,1,2,…`. Equivalently,

\[
F(0)=0,\qquad F(i)\le1+\max_{j<i}F(j).
\]

Every onto `F` can be put uniquely in this form by relabeling `B`.
The same relabeling is applied to `G`, and the script still
enumerates **all** onto `G` maps to those labels. Thus no
possibility is lost. All conditions (1)–(3) and the subsequent
coverage checks are invariant under this simultaneous relabeling.

There are 14,004 normalized compatible map cases. Filtering the
degree-five candidates by (3) gives this inventory:

| `|B|` | Cases with 0 candidates | Cases with 1 | Cases with 2 | Cases with 3 |
| ---: | ---: | ---: | ---: | ---: |
| 2 | 408 | 48 | 24 | 24 |
| 3 | 11,052 | 144 | 72 | 72 |
| 4 | 2,160 | 0 | 0 | 0 |

These four candidate-count columns leave respectively 12, 11,
10, and 8 mandatory low-output triples uncovered, even when every
remaining candidate is allowed simultaneously. Every case therefore
contradicts the central-column triple lemma. This proves the theorem.

## 3. Independent finite regression for five degree-four vertices

The same executable also checks

```text
python3 scripts/1485_m3_sharp_fiber_check.py --size 5
```

Here joint injectivity gives `5≤|B|²`, so `|B|≥3`. The
[opposite-parity theorem](1485_order_twenty_four_three_central_reduction.md#predecessor-and-successor-parities-are-opposite-and-constant)
therefore applies: all predecessor profiles have one permutation
parity, and all successor profiles have the opposite parity. Its
proof uses `|B|≥3`, not an order-24 assumption.

Both opposite-parity choices are enumerated. Specifically, the code
starts from all 36 permutation-profile pairs and retains disjoint
five-element collections for which `|V_a∩U_c|=1` for every
ordered pair `a,c`. There are exactly

\[
2\binom95=252
\]

such collections: each opposite-parity choice gives a nine-cell
profile grid. There is no parity quotient and no choice of a single
representative family.

The preliminary triple-coverage test leaves 162 collections.
Enumerating normalized onto sharp maps to `B` of sizes three,
four, and five, with the same conditions (1)–(2), gives:

| `|B|` | Normalized map cases | Degree-five candidates after (3) |
| ---: | ---: | ---: |
| 3 | 89,100 | 0 in every case |
| 4 | 213,408 | 0 in every case |
| 5 | 19,440 | 0 in every case |

All 321,948 cases therefore contradict the
[analytic necessity of degree five](1485_three_central_requires_five.md).
The script also checks the more concrete low-output triple failure
in every case. This finite regression is independent of any later
analytic simplification of the five-vertex case.

For a cross-check of the earlier result, `--size 3` reproduces the
three-vertex exclusion with the same codomain normalization: 1,956
collections, 24 preliminary survivors, and 216 compatible map cases,
all contradictory. This agrees with the older 720-case check that
keeps every codomain labeling.
