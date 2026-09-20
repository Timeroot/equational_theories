# Singleton central labels separate at the boundary first-output degree

Research note, 20 September 2026. These are analytic finite E1485
theorems, not Lean declarations. No enumeration or solver result is used.

Let `r≥3` be the minimum translation degree, let `Z` be the
central class of size `m`, and suppose

\[
r\le m\le2r-2.
\]

Write `P_u,C_u` for the central predecessor and successor blocks
of a top vertex `u`. Suppose the least degree of a noncentral
product of two tops is `p=2r−1`. Define the sets of singleton
labels

\[
S_C=\{c\in Z:\text{some top has }C_u=\{c\}\},\qquad
S_P=\{c\in Z:\text{some top has }P_u=\{c\}\}.
\]

**Theorem.** These two label sets are disjoint. Moreover

\[
\boxed{|S_C|,|S_P|\ge2r-m,\qquad
S_C\cap S_P=\varnothing.}                               \tag{1}
\]

## 1. Every singleton omission produces a crown

Every partition of `m` labels into `r` nonempty blocks has at
least `2r−m≥2` singleton blocks. Fix a top `u` with
`C_u={c}`. For a top `d∈Row(c)` whose successor block
`C_d={z}` is singleton, choose a least noncentral output

\[
a\in u*Col(z).
\]

The [row-local ordered-degree bound](1485_first_top_output_fibers.md#5-a-row-local-degree-bound)
puts its degree at most `2r−1`, hence exactly `p` by the
global first-output assumption. The same
[exact replacement argument](1485_maximal_central_block_first_output_gap.md#2-every-omitted-central-row-point-occurs)
gives

\[
Row(a)=L_u^{-1}(a)\ \sqcup\bigl(Row(c)\setminus\{d\}\bigr).
                                                               \tag{2}
\]

For completeness, all members of `Row(a)` have their `L_u`
image in the auxiliary set `u*Col(z)`. Descent at
the ordinary middle `a` permits only the output `a` or the
central output `c`. Their two fibers have `r` elements each.
The central input `c*z=d` cannot be in `Row(a)`, whose
intersection with `Col(z)` is its distinct input at `a`.
Removing that one point leaves exactly `2r−1=|Row(a)|`
points, proving (2).

The top successor blocks of `a` partition `Z`. The retained
`r−1` tops in (2) already cover every central label except
`z`. Their replacement therefore consists of exactly one top,
with successor block `{z}`. The
[first-output fiber theorem](1485_first_top_output_fibers.md)
gives equal top-profile sizes, so both profiles have size `r`.
Their central-middle matrix is the crown `J_r-I_r`.

No maximal-block hypothesis on `P_u` is needed here: choosing
a **singleton omission** itself forces the crown size.

## 2. Singleton successor labels cannot also be predecessor labels

Let `U,V` be the crown profiles just obtained. The row at `u`
is one on the `r−1` retained members of `Row(c)` and zero
on their replacement. No other member of `U` can have `c`
in its successor block, since its crown row would then have the
same `r−1` ones and be identical to the row at `u`.

Consequently a retained top with predecessor block `{c}` would
give a column with just one one, instead of the required
`r−1≥2`. It cannot occur.

There are at least two singleton omissions in `Row(c)`, so any
chosen member of `Row(c)` can be retained by choosing a different
one. Thus **no member of `Row(c)` has a singleton predecessor
block**. Such a block would necessarily be `{c}`. In particular
`c∉S_P`. This proves `S_C∩S_P=∅`.

Each central row has at least `2r−m` distinct singleton successor
labels, and each central column has at least that many singleton
predecessor labels. This proves the remaining assertions of (1).

## 3. A general central-cardinality consequence

The two disjoint label sets fit inside `Z`, so

\[
2(2r-m)\le m,\qquad
\boxed{m\ge\left\lceil\frac{4r}{3}\right\rceil.}         \tag{3}
\]

In particular, if `r≤m<4r/3`, the first noncentral top-product
degree is at most `2r−2`: a singleton row gives the preliminary
bound `2r−1`, and (3) excludes equality. This concerns the
first noncentral top product, not necessarily the least noncentral
degree of the entire magma.

There is also a useful bound on every central block size `b`.
A partition containing that block has at least

\[
2(r-1)-(m-b)=2r-m+b-2
\]

singleton blocks among its other `r−1` blocks. Thus the
corresponding singleton-label set has at least that size, while
the opposite set has at least `2r−m` by (1). Disjointness gives

\[
\boxed{b\le3m-4r+2.}                                    \tag{3a}
\]

This argument applies to both predecessor and successor blocks.
The displayed lower bound on the other singleton blocks may be
weaker than (1), but that does not affect the inequality.

If `r≥4` and `m=4r/3`, equation (3a) makes every central
block have size at most two. The
[small-central-block first-output gap](1485_small_central_blocks_first_output_gap.md)
then excludes `p=2r−1`. Consequently the boundary degree
requires the strict bound

\[
\boxed{r\ge4\quad\Longrightarrow\quad
m>\frac{4r}{3},\quad\text{equivalently }\quad
m\ge\left\lfloor\frac{4r}{3}\right\rfloor+1.}           \tag{3b}
\]

This improves (3) exactly when `r` is divisible by three.

## 4. At minimum four and central count six, the triple blocks are fixed

Specialize to `r=4,m=6,p=7`. Each of `S_C,S_P` has at
least two labels. A predecessor block of size three fills one
block of a central-column partition; the other three blocks are
singletons. Thus the complement of every predecessor triple is
contained in `S_P`. Dually, the complement of every successor
triple is contained in `S_C`.

If both a predecessor triple and a successor triple occur,
then `|S_C|,|S_P|≥3`. By disjointness they are complementary
triples, and necessarily

\[
\boxed{
P_u\text{ of size three}\Longrightarrow P_u=S_C,\qquad
C_v\text{ of size three}\Longrightarrow C_v=S_P.
}                                                        \tag{4}
\]

This applies even when the two triple blocks occur at different
tops. The general containment restriction below strengthens this:
the two triple orientations cannot coexist at all. In particular
it excludes `(3,3)` without needing the separate
[complementary-triple argument](1485_min_four_six_central_disjoint_triples.md),
which remains an independent alternative for that special case.

## 5. Containment of a nonsingleton-sided block is restricted

Return to the general assumptions `r≥3`, `m≤2r−2`,
`p=2r−1`. If a top `v` has `|C_v|≥2`, there is no
different top `w` satisfying

\[
P_w\subseteq P_v,\qquad P_w\cap S_C\ne\varnothing.       \tag{5}
\]

To prove this, choose `c∈P_w∩S_C` and a top `u` with
`C_u={c}`. Both `v,w` belong to `Row(c)`. Among its at
least two singleton successor-block omissions, choose one different
from `w`; none equals `v`, whose successor block is nonsingleton.
The crown obtained in Section 1 retains both `v,w`.

The predecessor inclusion in (5) makes the column at `w`
entrywise at most the column at `v`. Both have exactly `r−1`
ones, so the columns are equal. Distinct crown columns cannot be
equal, which proves the restriction. Notice that the forbidden
inclusion includes equality of the two predecessor blocks.

In particular,

\[
\boxed{|C_v|\ge2,\quad P_v\subseteq S_C
\quad\Longrightarrow\quad |P_v|\le m-r.}                 \tag{6}
\]

Indeed choose a central label `z∉C_v`. Such a label exists:
`C_v` is one block in an `r`-block central-row partition and
therefore has size at most `m−r+1<m`. The `r` predecessor
blocks of `Col(z)` partition `Z`, and none belongs to `v`.
By (5), none is contained in `P_v`: a nonempty subset of
`P_v⊆S_C` would meet `S_C`. Each therefore has at least
one element outside `P_v`. Summing gives

\[
|P_v|
=\sum_{w\in Col(z)}|P_w\cap P_v|
\le\sum_{w\in Col(z)}(|P_w|-1)
=m-r.
\]

There is a dual statement: if `|P_v|≥2`, no different top
has `C_w⊆C_v` with `C_w∩S_P≠∅`, and
`C_v⊆S_P` implies `|C_v|≤m−r`.

## 6. Triple blocks at minimum four have only one possible orientation

Again let `r=4,m=6,p=7`. Suppose a predecessor triple occurs.
Section 4 gives `|S_P|≥3`. If also `|S_C|≥3`, separation
would make the two singleton-label sets complementary triples,
and every predecessor triple would equal `S_C`.

The [maximal-block theorem](1485_maximal_central_block_first_output_gap.md)
excludes a singleton successor block on that top, so `|C_v|≥2`.
Equation (6) would then give `3=|P_v|≤m−r=2`, a contradiction.
Together with the lower bound in (1), this proves

\[
\boxed{
\text{A predecessor triple forces }|S_C|=2;\qquad
\text{a successor triple forces }|S_P|=2.
}                                                        \tag{7}
\]

A successor triple also forces `|S_C|≥3`, so both triple
orientations cannot occur. In particular no top has profile
`(3,3)`, and a `(3,2)` top and a `(2,3)` top cannot coexist.
The remaining single-orientation case is excluded in the
[two-singleton-label argument](1485_min_four_six_central_two_singleton_labels.md).
Combined with the small-block gap, this gives the separate
[complete six-central degree-seven exclusion](1485_min_four_six_central_seven_exclusion.md).
The containment theorem on this page is one ingredient of that
proof, not by itself an exclusion of either remaining orientation.
