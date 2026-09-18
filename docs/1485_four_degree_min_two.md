# Four translation degrees at minimum degree two

Research note, 18 September 2026. This proves the following finite
spectrum statement:

**Theorem.** If a finite E1485 magma has minimum translation degree two
and exactly four translation degrees, its order is **32**.

This has the proposed form `32=2·4²`. This is an order restriction. It
does not classify models with more degree values or other minimum
degrees. No assertion here is a Lean declaration.

We use the [full central core](1485_full_central_core.md), the
[neighbor gaps](1485_min_two_neighbor_gap.md), the
[sharp-regular four-degree theorem](1485_four_degree_regular_gap.md), and the
[minimum-degree-two exclusion at order 24](1485_order_twenty_four_min_two.md).

## The four classes

Degree four occurs whenever the minimum is two and some larger degree
occurs. Degree reciprocity and the hypothesis of exactly four degree
values therefore give

\[
2,\quad4,\quad b,\quad2b,
\qquad n=4b,\quad b>4.
\]

Indeed the reciprocal pairs are `2,2b` and `4,b`; the alternative
`b<4` would require degree three, which is excluded. The neighbor-gap
theorem also excludes `b=5`.

Write `Z,A,H,T` for these four classes. More generally, the first
count below works with degrees `r,2r,b,2b` and `n=2rb` under the full
central-core hypothesis. Each degree-`2r` vertex is sharp-regular.
Every vertex has `r` top neighbors in each direction.

Let `k_a` be the common sharp in-degree and out-degree of a high
vertex `a∈H`. The equality of these counts follows from reciprocal
neighbor balance: its non-top neighbors have degrees only `2r` and
`b`. Write `C` for the canonical `r`-regular relation. Its internal
part `R=C∩(H×H)` has in-degree and out-degree `r-k_a` at `a`.
Ordinary internal adjacency has degree `b-r-k_a`.

## A support bound for bad extensions

Fix an ordinary internal edge `a→u`. Every bad high extension
`a→u→c` has its good replacement in `A`: strict degree decrease
excludes another high middle, and central vertices cannot be adjacent
to the high endpoints. Therefore `c` belongs to

\[
K(a)=\{c\in H:a\Rightarrow\alpha\Rightarrow c
                 \text{ for some }\alpha\in A\}.
\]

There are `k_a` choices of the sharp successor `α`, and each has
`r` sharp successors in `H`. These sets are disjoint by unique
goodness, so

\[
\boxed{|K(a)|=r k_a.} \tag{1}
\]

If the edge belongs to `R`, its good extensions consist of `r` top
extensions, `k_u` sharp extensions into `A`, and `r-k_u` good high
extensions. It has exactly `b-2r` bad high extensions. Thus

\[
\boxed{aRu\quad\Longrightarrow\quad b-2r\le r k_a.} \tag{2}
\]

If the internal edge is outside `R`, none of its good extensions is
top. It instead has `2r-k_u` good high extensions and `b-3r` bad
high extensions. The corresponding bound is

\[
b-3r\le r k_a. \tag{3}
\]

## All four-degree models at minimum two are sharp-regular

Return to `r=2`. If a high vertex `a` were irregular, it would have
`k_a=1` and a successor in `R`. Equation (2) would give

\[
b-4\le2,
\quad\text{so}\quad b\le6.
\]

Since `b>4` and degree five is absent, this leaves only `b=6`.
But every degree-six vertex is sharp-regular by the neighbor-gap
theorem. This contradiction proves that every high vertex has sharp
in-degree and out-degree two. All four degree classes are consequently
sharp-regular.

The exact sharp-regular four-degree theorem now gives `b=4r=8`, and
therefore `n=4b=32`. This proves the theorem.

## An independent bound and saturation check

For completeness, the bad-extension support count gives an independent
short exclusion at order 40. Before using the exact cardinality theorem,
the conditional gap gives `b=6` or `b≥8`; the first possibility is
order 24 at minimum degree two, already excluded. Since `R` is empty,
(3) gives

\[
b-6\le4,
\quad\text{hence}\quad
\boxed{b\in\{8,9,10\}.} \tag{4}
\]

### Saturation excludes degree ten

Suppose `b=10`, so the order is 40. The central and top classes each
have size four. Sharp regularity and the sharp incidence between `A`
and `H` give

\[
|A|=|H|=16.
\]

Let `P,Q,D` be adjacency on `A→H`, `H→A`, and `H→H`.
The matrices `P,Q` are two-regular, and `D` is six-regular in both
directions. Put `K=QP`. It is a zero-one matrix, four-regular in both
directions, indicating high endpoint pairs with a good middle in `A`.

For every edge `aDu`, there are four bad high extensions, by (3).
They all lie in the four-element set `K(a)`, by (1), so they exhaust
that set. Consequently for `K_{ac}=1`, all six internal successors
of `a` lead to `c`; thus `(D²)_{ac}=6`.

The regular four-degree count gives `E=J-K`, where `E` indicates
the unique good high middle. Explicitly, `K` has row sum four, while
the good high paths have row sum `6·2=12`; these disjoint supports
exhaust all sixteen endpoints. Where `K_{ac}=0`, there is therefore
exactly one ordinary high middle. Altogether,

\[
\boxed{D^2=J_{16}+5K.} \tag{5}
\]

Both `Row_D(a)` and `Col_D(c)` have size six. Equation (5) now says

\[
K_{ac}=1
\quad\Longleftrightarrow\quad
\operatorname{Col}_D(c)=\operatorname{Row}_D(a). \tag{6}
\]

Thus the four entries in any row of `K` form exactly one class of
identical columns of `D`. Every column index belongs to some such
class because every column of `K` has four entries. Hence **every
class of identical columns of `D` has cardinality four**.

Each row of `D` is constant on each class of identical columns. Its
row sum must therefore be divisible by four. This contradicts the
row sum six, excluding `b=10`.

This independent saturation argument leaves `b=8,9` in (4). The exact
cardinality theorem used above excludes `b=9` as well.

## Scope of the exclusions

In particular the minimum-degree-two cases of orders 28 and 40 are
excluded, as is the four-degree minimum-two case at order 36.
This note alone does not exclude order 40 at every possible
minimum degree; its potential degree pattern `4,5,8,10` lies outside
the theorem's scope.
