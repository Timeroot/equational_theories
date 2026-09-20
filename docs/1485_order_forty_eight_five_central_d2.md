# Order forty-eight, five central vertices: excluding two double blocks

Research note, 19 September 2026. This is a **finite-assisted
exclusion**, not a purely analytic classification and not a Lean proof.
The mathematical reduction is given below; its final finite step is
checked by the self-contained standard-library Python program
[`1485_n48_five_central_d2_check.py`](../scripts/1485_n48_five_central_d2_check.py).
No solver result or conjectural premise is used.

Under the assumptions `n=48`, `r=4`, and `|Z|=5`, write `N_ij`
for the number of tops with `i` central predecessors and `j`
central successors. The
[central moment calculation](1485_order_forty_eight_five_central.md)
gives

\[
(N_{11},N_{12},N_{21},N_{22})=(5+4d,5-2d,5-2d,d),
\qquad d\in\{0,1,2\}.
\]

**The finite check excludes `d=2`.** Thus any model in this branch
must have `d=0` or `d=1`. This does not exclude the entire
five-central branch or order 48.

## 1. Complete central-incidence normalization

In the case `d=2` there are two tops of type `(2,2)`, one of
type `(2,1)`, one of type `(1,2)`, and thirteen of type `(1,1)`.
For a top `t`, let `P_t,C_t` denote its central predecessor
and successor sets. The rectangles `P_t×C_t` partition `Z×Z`,
because every central-to-central endpoint pair has exactly one
ordinary middle. In addition,

\[
|C_t\cap P_v|\le1\quad(t,v\in T).                    \tag{1}
\]

Every central row has four tops and covers five central labels
by their successor blocks. Thus exactly one of its four tops
has a two-element successor block. Consequently the predecessor
blocks of the three tops having two-element successor blocks
partition `Z`. The dual statement holds as well.

Label `Z={0,1,2,3,4}`. We may therefore fix the predecessor
sets of the two `(2,2)` tops to be `{0,1}` and `{2,3}`.
The predecessor set of the `(1,2)` top is then `{4}`. Let the
successor sets of the `(2,2)` tops be disjoint pairs `c_0,c_1`;
their remaining central label is the successor of the `(2,1)`
top. The remaining predecessor pair `p` and successor pair `c`
are otherwise arbitrary two-element subsets.

There are only two restrictions to check at this stage:

1. The `2×1` rectangle and `1×2` rectangle must not overlap.
2. No two-element predecessor block may equal a two-element
   successor block, by (1).

The four nonsingleton rectangles then cover twelve central
endpoint pairs. Each of the thirteen uncovered pairs supplies
exactly one `(1,1)` top. This gives **all 984 normalized labeled
central tilings** examined by the program. Some are isomorphic;
retaining them all is harmless. No additional relabeling quotient
or unproved canonical-form assumption is used.

## 2. All possible degree-six profiles

Let `a` have degree six. Write `U,V` for its top predecessor
and successor sets. Their central blocks satisfy

\[
\{P_u:u\in U\}\text{ partitions }Z,
\qquad
\{C_v:v\in V\}\text{ partitions }Z.                  \tag{2}
\]

All non-top neighbors of `a` are sharp degree-eight neighbors.
Reciprocal-neighbor balance makes its sharp in- and out-counts
equal, so

\[
|U|=|V|\in\{3,4,5\}.
\]

The first-output fiber calculation says that the central-middle
matrix on `U×V` is two-regular:

\[
K_{uv}=|C_u\cap P_v|\in\{0,1\},
\qquad \sum_v K_{uv}=\sum_u K_{uv}=2.                 \tag{3}
\]

The program enumerates every pair of partitions (2), retains
equal cardinalities and (3), and records its good top pairs

\[
G(U,V)=\{(u,v)\in U\times V:K_{uv}=0\}.
\]

These are exactly the top endpoint pairs whose product would
be this degree-six vertex: a bad degree-six middle can only
be replaced by a central middle. In particular two different
degree-six vertices cannot have intersecting sets `G(U,V)`.
There is no assumption that an enumerated profile is realizable.

### An analytic reduction of the profile types

The following observations are not needed by the checker, which
keeps all sizes three through five, but reduce its profile geometry.

View `K` as a two-regular bipartite graph. Each component is
an even cycle. In a component with `l≥3` rows and `l` columns,
let `a` count rows whose underlying `C` block has size two,
and `b` count columns whose underlying `P` block has size two.
A singleton-`C` row uses one central label for both neighbors.
Neither neighboring column can use only that label: its other
neighboring row would then also meet the singleton row's label,
creating an entire square component. Both neighboring columns
therefore have double `P` blocks. Counting those edges gives

\[
l-a\le b.
\]

If equality holds with `0<a<l`, the edges from the `l−a`
singleton rows exhaust the degrees of the `b` double columns.
Those vertices form a proper union of connected components,
contrary to the chosen cycle being connected. Thus

\[
a+b\ge l+1
\quad\text{unless }(a,b)=(0,l)\text{ or }(l,0).        \tag{4}
\]

For a size-five profile, all predecessor `P` blocks are
singleton. There is at most one double `C` block, belonging
to the unique `(1,2)` top. Dually there is at most one double
`P` block among its successors. Equation (4) excludes every
nonsquare component. But squares cannot partition five rows.
Hence **a degree-six vertex cannot have top-profile size five**
in the `d=2` case.

For a size-four profile, there is exactly one double predecessor
`P` block and three singleton ones. Thus it has at most two
double `C` blocks: one at that double-`P` top and one at the
unique `(1,2)` top. Dually there are at most two double `P`
blocks among its successors. If `K` were an eight-cycle,
(4) would require at least five such double blocks in total,
but there are at most four. Thus **every size-four profile has
two disjoint square components**. Size-three profiles have a
six-cycle. This still does not replace the final finite tiling
and coverage check by an analytic argument.

## 3. A mandatory output in each central-column image

If `u` is top and `|C_u|=1`, the
[row-local first-output bound](1485_first_top_output_fibers.md#5-a-row-local-degree-bound)
shows that **for every central `z`** the image `u*Col(z)`
contains a noncentral output of degree at most seven. The only
possible such degree at order 48 is six.

Consequently, for each pair `(u,z)` with `|C_u|=1`, some
degree-six profile must have a good pair `(u,v)` with `z∈C_v`.
The check first lists all candidate profiles witnessing every
one of these requirements.

* In **976 tilings**, some requirement has no candidate profile.
* In the other **eight tilings**, there are two requirements such
  that every choice of a candidate for each uses distinct profiles
  with intersecting good-pair sets. Product uniqueness forbids
  realizing both requirements.

Thus none of the 984 central tilings can occur. The second test
is only a pairwise incompatibility check; no satisfiability solver
or search through potential magma operations is involved.

Run the complete exact check with:

```sh
python3 scripts/1485_n48_five_central_d2_check.py
```

The program asserts both the exhaustive-case counts and the
absence of an unexcluded tiling. A purely analytic replacement
for the 984-case central/profile check would be desirable, but
is not claimed here.
