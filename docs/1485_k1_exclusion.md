# Excluding the two-degree case with sharp degree one

Research note, 18 September 2026. Assume the finite-structure results in
[the graph note](1485_graph_research.md), the moments in
[the two-degree note](1485_two_degree_research.md), and strict degree
decrease from [the projection note](1485_image_research.md).

**Theorem.** In a finite E1485 magma with exactly two translation degrees,
if even one high-degree vertex has exactly one central successor, then the
minimum translation degree is one. Thus, when the minimum translation
degree exceeds one, every high vertex has at least two sharp successors
and at least two sharp predecessors.
In particular, the proposed order-twelve case with degrees three and four
and nine high vertices of sharp degree one does not exist.

Write the two degrees as `r<s`, the order as `n=rs`, and the central and
high sets as `Z,H`, of sizes `m,h`. First assume all `k_v=1`; the final
section reduces the theorem's hypothesis to this case. The moment identities with every
`k_v=1` give

\[
 h=mr=m^2,
 \qquad m=r,\quad h=r^2,\quad s=r+1.
\]

Each high vertex has exactly `r` high successors and `r` high
predecessors. Let `D` be the adjacency matrix restricted to `H`.

## Every bad path has a central good replacement

This observation applies to every finite two-degree model, without the
sharp-degree-one assumption. If `a→b→c` is a bad path, write `c=b*t`.
Then `b∈Row(a)` and

\[
 P_t(b)=a*(b*t)=a*c\ne b.
\]

Strict degree decrease gives `d(a*c)<d(b)`. There are only two degrees,
so `b` is high and `a*c` is central. Consequently a pair of high endpoints
without a central common middle has exactly one ordinary two-edge path,
whose middle is high.

## Exactly one high two-edge path for every high endpoint pair

We prove

\[
 \boxed{D^2=J_{r^2,r^2}.} \tag{1}
\]

The preceding observation already handles endpoint pairs without a
central common middle. Suppose instead that `a→z→v` with `a,v∈H`
and `z∈Z`. Let `c` be the unique central successor of `v`.
Every path containing a central vertex is good, so `z*c=v` and `a*v=z`.

Consider the idempotent `P_c(t)=a*(t*c)`. Its image is contained in
`Row(a)` and has rank `r`, because `c` is central. Its fixed points in
`Row(a)` are exactly its image. The set `Row(a)` has `r+1` elements:
the unique central successor `z`, and `r` high vertices. The central point
`z` is fixed, because `a→z` is sharp. Strict degree decrease says that
any point of `Row(a)` moved by `P_c` must map to `z`. Since the rank is
`r`, exactly one high point of `Row(a)` is moved.

For a high point `t∈Row(a)`, the following are equivalent:

\[
 P_c(t)=z\quad\Longleftrightarrow\quad t*c=v
 \quad\Longleftrightarrow\quad t\to v. \tag{2}
\]

For the first forward implication, `a*(t*c)=z` implies the edge
`z→t*c`; the product `t*c` also has an edge to `c`. The path
`z→t*c→c` is good by centrality, so `t*c=z*c=v`. The reverse implication
uses `a*v=z`. For the second equivalence, one direction follows from
the product path, and the other from goodness of `t→v→c`.
Thus the unique moved high point is exactly the unique high common
middle from `a` to `v`. This proves (1).

## Each high edge has exactly one bad high extension at either end

Fix a high edge `a→b`. The fiber `{c:a*c=b}` has size `n/d(a)=r`.
Exactly one of its elements is central: the unique central successor
of `b`. Hence `a→b` has exactly `r−1` good extensions whose last
vertex is high. The vertex `b` has `r` high successors, so precisely
one high successor makes a bad path. Dually, each high edge has
precisely one bad high predecessor.

More generally, in any two-degree model, each high edge has precisely
`s−r` bad high extensions and `s−r` bad high predecessors. Indeed, if
the middle vertex has `k` central successors, the total number of high
extensions is `s−k`, while the good high extensions number `r−k`.

## A bad path has at most two high five-cycle completions

There are high edges, and each has a bad extension, so choose a bad high
path `a→b→c`. Since (1) holds and `D` has row sum `r`,

\[
 D^3=rJ.
\]

Thus there are exactly `r` ordered pairs `(d,e)∈H²` completing it to
a high five-cycle

\[
 a\to b\to c\to d\to e\to a.
\]

For each such completion, at least one of `e→a→b` and `b→c→d`
must be bad. Otherwise the five-cycle law applied in the cyclic order
`e,a,b,c,d` would make `a→b→c` good.

There is at most one completion with `b→c→d` bad: the bad extension
of `b→c` uniquely specifies `d`, and (1) then uniquely specifies the
middle `e` of `d→e→a`. There is at most one completion with
`e→a→b` bad, by the dual argument. Consequently

\[
 \boxed{r\le2.} \tag{3}
\]

The case `r=2` is excluded by the elementary bit argument in the
[two-degree note](1485_two_degree_research.md#excluding-the-degree-pair-23).
Therefore `r=1`, as asserted. The remaining order is two, and the
two-element NAND magma realizes it.

## One sharp-degree-one vertex forces all sharp degrees to be one

Now assume only that one high vertex `a` has `k_a=1`, with unique
central successor `z`. Put `t=s−r>0`. For every high vertex `v` with
central predecessor `z`, choose any central successor `c` of `v`.
The rank argument above applies without change, except that `Row(a)`
has size `s` and `P_c` has rank `r`: exactly `t` high points move, and
they all map to `z`. The equivalences (2) still apply. Therefore there
are exactly `t` high common middles from `a` to each `v∈Row(z)`.
There are `r` such endpoints `v`, so the total number of bad high
two-edge paths starting at `a` is `rt`.

There are no other bad paths from `a`, because every bad path must have
a central good replacement, and `z` is its only possible central middle.
On the other hand, `a` has `s−1` high successors and every high edge
has exactly `t` bad high extensions. Thus the same number is `t(s−1)`.
Cancelling positive `t` gives `s=r+1`.

The established inequalities `m≥r` and `h≥r²`, together with
`m+h=r(r+1)`, now give `m=r` and `h=r²`. The first moment says
`Σ_{v∈H}k_v=mr=r²=h`. Since every `k_v≥1`, all sharp degrees on `H`
are one. The preceding proof applies and gives `r=1`.

This proof uses no exhaustive search or unproved classification. Its
exclusion of the order-twelve **degree pair `(3,4)`** is a consequence
of strict degree decrease, uniform translation fibers, and the five-cycle
law. It does not exclude an order-twelve model with other degrees.

## Consequences for the smallest degree and the general bound

Suppose `r>1`. We have proved `2≤k_v≤r` for all `v∈H`. Replacing
the bound `k_v≥1` in the moment argument by this stronger bound gives

\[
 (k_v-2)(k_v-r)\le0,
 \qquad m^2-r(r+4)m+2r^2s\le0.
\]

Consequently

\[
 \boxed{s\le\left\lfloor\frac{(r+4)^2}{8}\right\rfloor.} \tag{4}
\]

More generally, if every `k_v≥q>0`, the same argument gives
`s≤floor((r+2q)²/(4q))`.

For `r=3`, all sharp degrees are at least two. The good-high-path
endpoint inequality from the two-degree note would require
`k_a+k_c≤3` if `a*c` were high. This is impossible. Thus every
product of two high vertices is central, or `CB=J_{h,h}`.
Together with `BC=J_{m,m}`, this forces `k_v=r` for every high vertex:
the equality `(BC)B=B(CB)` compares the column sum `k_v` of `B`
with its row sum `r`. Now `BC=J` gives `m=r²`, and `CB=J` gives
`h=r²`. Hence

\[
 \boxed{r=3\ \Longrightarrow\ s=6,\ n=18.} \tag{5}
\]

The same argument works whenever `min k_v>r/2`. In particular the
two-degree possibilities with minimum degree two or three now have the
conjectured cardinality `2r²`.

For distinct primes `p<q`, a model of order `pq` would have exactly the
two degrees `p,q`: degree one would give a constant-row model and hence
a power-of-two order. Thus (4) improves the earlier semiprime bound to
`q≤floor((p+4)²/8)`. This remains only a necessary condition, not a
complete exclusion of odd semiprime orders.

## A limitation of the high-adjacency argument

The identity `D²=J` above uses sharp degree **one**. It is false in
general, even when all high vertices have the same sharp degree. For
the explicit order-eight table in the
[projection note](1485_image_research.md#central-coordinates-need-not-have-uniform-reverse-fibers),
the high vertices, ordered as `0,3,4,5`, have adjacency matrix

```text
D = 1 1 0 0       D² = 1 1 1 1
    0 0 1 1            1 1 1 1
    1 0 0 1            1 2 1 0
    0 1 1 0            1 0 1 2
```

Here every high sharp degree is two. Thus simply replacing one by an
arbitrary constant sharp degree in the five-cycle proof is not valid.
