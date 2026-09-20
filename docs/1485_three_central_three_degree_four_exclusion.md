# Three central vertices cannot have exactly three degree-four vertices

Research note, 19 September 2026. This is a finite E1485 proof using
a directly executable profile enumeration. It does not invoke SAT,
an ATP, or enumeration of magma tables, and is not yet formalized
in Lean.

**Theorem.** At minimum translation degree three, a magma with exactly
three central vertices has at least four degree-four vertices.

The [singleton case](1485_three_central_singleton_exclusion.md) and
[two-vertex case](1485_three_central_two_degree_four_exclusion.md)
have already been excluded. Suppose the degree-four class is now
`A={a₀,a₁,a₂}`. Write `B` for its reciprocal degree class.

## 1. The same top-profile and companion restrictions

We use the nine-top grid, central-pair set `K`, 36 possible
degree-four permutation profiles, and 729 possible degree-five
profiles from the two-vertex note. The three degree-four good sets
are pairwise disjoint; let their union be `G_A`.

A degree-five candidate with top profiles `U,V` has good set

\[
G=(U\times V)\setminus(K\cup G_A),
\]

with one or two entries in every row and column, at most four good
entries in total, and a degree-four companion at every good position
in a row or column containing two good entries. These are necessary
conditions, not a claim that the candidates coexist.

The first enumeration checks all 1,956 disjoint triples of the 36
degree-four profiles. For each triple, form `G_A` together with the
union of **all** candidate degree-five good sets. The
[central-column triple condition](1485_three_central_singleton_exclusion.md#1-each-central-column-triple-contains-a-degree-four-or-degree-five-output)
and its dual eliminate all but 24 collections.

Each remaining collection has three pairwise-disjoint predecessor
transversals and three pairwise-disjoint successor transversals,
paired in some bijection. This description is checked by the script;
it is not assumed to reduce the enumeration.

## 2. Sharp maps and mixed degree-four/degree-five products

Each member of `A` has one sharp successor and predecessor. Denote
the two maps by

\[
F,G:A\longrightarrow B.
\]

Both are onto, and `(F,G)` is injective: two vertices with the same
pair would give two good middles of a sharp `B→A→B` path.
Consequently `2≤|B|≤3`. With labeled `A` and `B`, there are
24 onto jointly injective pairs when `|B|=2`, and 36 when `|B|=3`.

For `a,c∈A`, if `F(a)≠G(c)`, their ordinary middles are all
top. A bad top middle cannot have the same degree as a good top
middle. Thus there is exactly one, giving

\[
F(a)\ne G(c)\quad\Longrightarrow\quad
|TopSucc(a)\cap TopPred(c)|=1.                    \tag{1}
\]

Now let `x` have degree five, with top profiles `U,V`. Besides
its three top predecessors, `x` has two non-top predecessors, at
least one sharp. Its only possible non-sharp predecessor is a
single vertex of `B`: a non-top, non-sharp neighbor has
complementary degree strictly between three and five, hence four.

Consider the endpoint pair `(a,x)`. The ordinary successors of
`a` are `TopSucc(a)` and `F(a)`. Unless `F(a)` is that one
non-sharp `B` predecessor of `x`, all ordinary middles of `(a,x)`
are top, and their number must be one. Therefore all exceptions

\[
E_F(x)=\{a\in A:|TopSucc(a)\cap U|\ne1\}
\]

must have the **same** `F`-value. Dually all exceptions

\[
E_G(x)=\{a\in A:|TopPred(a)\cap V|\ne1\}
\]

must have the same `G`-value. The filter used is exactly

\[
\boxed{|F(E_F(x))|\le1,\qquad |G(E_G(x))|\le1.}   \tag{2}
\]

If `x` has two sharp neighbors on a side, the corresponding
exceptional set must actually be empty. Allowing (2) is a safe
overapproximation; the enumeration does not require that stronger
condition.

## 3. Every compatible sharp-map case still misses required triples

For each of the 24 profile collections, enumerate the onto jointly
injective sharp-map pairs, retain those satisfying (1), and filter
its degree-five candidates by (2). There are 720 profile/map cases
after (1). Their exact inventory is:

| `|B|` | Remaining degree-five candidates | Missed low-output triples, including duals | Cases |
| ---: | ---: | ---: | ---: |
| 2 | 0 | 18 | 192 |
| 2 | 3 | 12 | 96 |
| 3 | 0 | 18 | 432 |

In particular, even after taking the union of all remaining
degree-five good sets, every case violates the mandatory degree-four
or degree-five output condition on some central-column triple or
its dual. This proves the exclusion.

Run the check with

```text
python3 scripts/1485_m3_three_degree_four_check.py
```

It reuses the candidate and triple-coverage helpers from the
two-vertex checker. The original two-vertex inventory is unchanged.
All profile collections and labeled sharp maps are enumerated
directly, without a canonicalization assumption.
