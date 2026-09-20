# Six central vertices and a degree-seven first top output

Research note, 19 September 2026. These are analytic intermediate
reductions, not a Lean formalization.

**Completed, 20 September:** the entire case considered here is now
[excluded analytically](1485_min_four_six_central_seven_exclusion.md).
The sharper general result covers
[two extra central vertices at every minimum degree at least four](1485_two_extra_central_first_output_gap.md).
The original reductions below are retained for reference; statements
about a branch remaining open describe their historical stopping point,
not the current frontier.

**Subsequent improvement, 20 September:** the general
[maximal-central-block theorem](1485_maximal_central_block_first_output_gap.md)
now excludes every `(3,1)` or `(1,3)` top profile under these
hypotheses. After duality, only the `(2,1)` witness from §4
remains. The earlier `(3,1)` containment lemma in §5 is retained
as part of the route to that stronger theorem.
The [complementary-triples theorem](1485_min_four_six_central_disjoint_triples.md)
also excludes a top with disjoint three-element predecessor and successor
blocks. Neither result alone excludes the remaining `(2,1)` witness.

Assume minimum translation degree four, exactly six central vertices,
and least noncentral top-product degree seven. Write `P_v,C_v` for
the central predecessor and successor sets of a top vertex `v`.
Each central row and column partitions six labels into four nonempty
blocks, so these sets have sizes at most three. Such a partition has
shape `3+1+1+1` or `2+2+1+1`.

The [first-output fiber theorem](1485_first_top_output_fibers.md)
says that a degree-seven top output `a` has equal top-profile sizes

\[
t=|TopPred(a)|=|TopSucc(a)|\in\{4,5,6\}.
\]

It has `7−t` non-top neighbors on either side, all contained in
every participating top translation fiber. The central-middle matrix
of its top profiles is three-regular.

## 1. A singleton central row gives an exact replacement

Suppose `C_u={c}` and `a=u*w` has degree seven. Choose
`z∈C_w`, and put `d=c*z`. Then

\[
\boxed{Row(a)=L_u^{-1}(a)\ \sqcup\ (Row(c)\setminus\{d\}).}
                                                               \tag{1}
\]

Indeed, the four-element set `S=u*Col(z)` contains exactly one
central output, namely `c`. In the row-local first-output argument,
every member of `Row(a)` lies either in the fiber at `a` or in
a lower-degree output fiber. By minimality of seven the only
possible lower output is `c`, so

\[
Row(a)\subseteq L_u^{-1}(a)\cup L_u^{-1}(c).
\]

The second fiber is exactly `Row(c)`: the top-to-central edge is
sharp, and both sets have size four. Its intersection with `Col(z)`
is the unique good middle `c*z=d`. On the other hand
`Row(a)∩Col(z)={w}`, by uniqueness at a central endpoint. The
point `d` cannot equal `w`, since their products under `L_u`
are respectively central and noncentral. Thus `d` is excluded
from `Row(a)`. The remaining union has seven points, exactly
`|Row(a)|`, which proves (1).

In particular the omitted top `d` is determined by `u,a` and
does not depend on the choice of `z∈C_w`. The top successor
partition of `a` is obtained from the central row `Row(c)` by
replacing `d` with the `t−3` good top inputs in `L_u^{-1}(a)`.
The central successor blocks of those new tops partition `C_d`.
They are disjoint from `Row(c)`, so their central predecessor
blocks do not contain `c`.

This gives the following more explicit possibilities:

| `t` | Replacement of the omitted central block |
| ---: | --- |
| 4 | One new top with exactly the same `C` block as `d` |
| 5 | A size-two block splits into two singletons, or a size-three block splits into a pair and a singleton |
| 6 | A size-three block splits into three singletons |

In the second row, the first alternative occurs in a central
partition `2+2+1+1`, while the second occurs in `3+1+1+1`.
The third row also requires `3+1+1+1`.

There are at least four distinct degree-seven outputs in every
top row with singleton `C_u`. To see this, take each of the
four tops `d∈Row(c)`, and choose `z∈C_d`. The row-local bound
produces a degree-seven output in `u*Col(z)`, whose omitted top
in (1) is exactly `d`. Different omitted tops require different
outputs. The column-dual statements hold for singleton `P` blocks.

## 2. A four-neighbor first output cannot have four singleton rows

Suppose `t=4`. Its central-middle matrix is, after reindexing,

\[
K=J_4-I_4.
\]

**Claim.** The four top predecessors cannot all have singleton
central successor blocks. Dually, the four top successors cannot
all have singleton central predecessor blocks.

For a contradiction write the predecessor singletons as
`C_{u_i}={c_i}`. The four labels are distinct, since the rows
of `K` are distinct. If the successors are `v_i`, the crown
matrix and the upper bound `|P_v|≤3` force

\[
P_{v_i}=\{c_j:j\ne i\}.                                    \tag{2}
\]

The blocks `C_{v_i}` partition all six central labels. In each
central column, its one top from this list has predecessor block
of size three. The other three predecessor blocks in that column
must therefore all be singletons. Consequently these four `v_i`
are all the globally occurring tops with predecessor-block size
three; every other top has predecessor-block size one.

The predecessor blocks of the four `u_i` partition six labels.
Thus exactly one of these tops, say `v_i`, has predecessor-block
size three, and the other three have size one. One of the uncovered
labels is `c_i`. The central row at `c_i` contains the other
three `v_j`, by (2), and precisely one further top `x`. Their
successor blocks partition the central set, so

\[
C_x=C_{v_i}.
\]

The top `x` has singleton predecessor block `{c_i}`. Since the
predecessor profile of `a` must cover `c_i`, it contains this
unique singleton-block top as well as `v_i`. These two members
have the same central successor set and hence identical rows in
`K`, contradicting the crown matrix. This proves the claim.

## 3. Equal central block sizes at every top are impossible

Suppose, provisionally, that every top satisfies `|P_v|=|C_v|`.
There cannot be a top with both blocks of size three. For if its
blocks are `A,B`, every column in `B` has that one three-element
predecessor block and three singleton predecessor blocks. Equality
of the two block sizes at every top makes all those other tiles
singletons in both directions. Hence each central row outside `A`
meets the three columns of `B` in three singleton tiles. Its fourth
tile has successor block `Bᶜ` and, by the assumed equality, a
three-element predecessor block.

That predecessor block cannot meet `A`: such a row would contain
the original tile with successor block `B` and this tile with
successor block `Bᶜ`, leaving no labels for the other two required
tops in the row. The block is therefore exactly `Aᶜ`. We have
obtained tops with predecessor blocks `A,Aᶜ`, both of size three.
The original successor block `B` cannot meet both in at most one
point, contrary to uniqueness of a central middle. This excludes
size three altogether under the provisional hypothesis.

All central blocks now have size at most two. A degree-seven first
output has one of the three top-profile sizes:

* If `t=4`, its predecessor block partition has shape `2+2+1+1`.
  The opposite successor blocks have the same sizes. The
  [singleton crown lemma](1485_two_set_crown_bound.md#1-a-singleton-permits-at-most-three-pairs)
  excludes the resulting crown intersection matrix with block sizes
  at most two.
* If `t=6`, all predecessor blocks, and hence all opposite successor
  blocks, are singletons. Section 1 would require a size-three
  central block to split into three singletons, which is impossible.
* If `t=5`, both lists of sets in the three-regular intersection
  matrix have sizes `2,1,1,1,1`. The following short count excludes
  this possibility as well.

For the last case, every label used by one of the four singleton
row sets must occur in exactly three column sets. There are only
six column-set memberships altogether, so at most two labels can
occur among those singleton rows. There cannot be just one: four
equal singleton row sets would give column sum at least four at
any column containing that label. Thus there are exactly two labels
`c,d`, each occurring in three column sets. All column memberships
are consequently in `{c,d}`. Their pair set is `{c,d}`, and their
four singletons split two at each label.

The columns with singleton `c` and singleton `d` now require each
label to occur in three row sets. The four singleton rows supply
only four occurrences altogether, so their pair set must also be
`{c,d}`. The row pair and column pair then intersect in two
points, contradicting uniqueness of the central middle.

All three profile sizes are impossible. Therefore

\[
\boxed{\text{Some top has }|P_v|\ne|C_v|.}                  \tag{3}
\]

## 4. A one-sided singleton witness always exists

In fact some top has one central block of size one and its other
block of size two or three. Suppose otherwise. Let `N_ij` count
tops with the indicated central block sizes. Only the types
`(1,1),(2,2),(2,3),(3,2),(3,3)` would remain. The two first
central incidence moments give `N_23=N_32=d`. Subtracting the
first moment from the mixed moment gives

\[
2N_{22}+7d+6N_{33}=12.
\]

It follows that `d≤1`; parity also makes `d` even. Thus `d=0`,
and all top block sizes agree, contrary to §3. Hence, after applying
the dual operation if necessary, one may choose a top `u` with

\[
\boxed{|C_u|=1,\qquad |P_u|\in\{2,3\}.}                    \tag{4}
\]

The row-local bound supplies a degree-seven first output in this
row. Since its predecessor blocks partition six labels and include
`P_u`, its top-profile size satisfies

\[
\boxed{
|P_u|=3\Longrightarrow t=4,\qquad
|P_u|=2\Longrightarrow t\in\{4,5\}.
}                                                          \tag{5}
\]

Thus an exclusion of these singleton-row witnesses with four or
five top neighbors would suffice; one need not start with a
six-neighbor witness. In the `|P_u|=3` branch, §2 also forces
one of the other top predecessors to have singleton `P` block
and nonsingleton `C` block: the three other predecessor blocks
are singletons, and their `C` blocks cannot all be singletons.

The six-central-vertex configuration is not excluded by this note.
The later maximal-block theorem linked above excludes the `(3,1)`
witness in (5); the `(2,1)` witness remains open.

## 5. A three/one witness must contain its singleton label

In the `|P_u|=3, C_u={c}` branch of §4, one necessarily has

\[
\boxed{c\in P_u.}                                         \tag{6}
\]

Here is a short proof using the exact replacement in §1. Choose
a degree-seven output in this row, and write `U,V` for its four
top predecessors and four top successors. Its central-middle matrix
is a crown. The row at `u` has ones at precisely the three
members of `V` lying in `Row(c)`.

No other member of `U` has a central successor block containing
`c`: such a row would already contain those same three ones, and
its required row sum three would make it identical to the row at
`u`, contrary to the crown matrix. Consequently none of the
three retained members of `Row(c)` can have predecessor block
`{c}`: its column in the central-middle matrix would have just
one entry, instead of three.

Suppose now that `c∉P_u`. The predecessor blocks of `U`
partition six labels into one triple and three singletons. There
is therefore an `x∈U` with `P_x={c}`. By the preceding
paragraph, `c∉C_x`.

The central column `Col(c)` also contains `u` with its triple
predecessor block and three singleton predecessor blocks. It
therefore contains a top `d` with `P_d={c}`, now with
`c∈C_d`. Thus `x,d` are distinct tops in `Row(c)`, both
with predecessor block `{c}`.

But §1 says that `V` retains three of the four members of
`Row(c)`, deleting only one. At least one of `x,d` would be
retained, contradicting the required three-entry column. This
proves (6). The later maximal-block theorem excludes the entire
three/one branch, including `c∈P_u`; the separate two/one branch
remains open.
