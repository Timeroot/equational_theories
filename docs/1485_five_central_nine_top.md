# Five central vertices force nine tops and no full central entries

Research note, 18 September 2026. This is an analytic finite proof,
not a Lean declaration. Assume a finite E1485 magma has minimum
translation degree three, five central vertices, and nine top vertices.
Write `B:Z→T`, `C:T→Z`, `K=CB`, `F=J−K`, and
`k⁻=Bᵀ1`, `k⁺=C1`.

**Theorem.** Neither `k⁻` nor `k⁺` has an entry equal to three.
Together with the [ten-top exclusion](1485_five_central_ten_top.md),
this shows that any finite minimum-degree-three model with five
central vertices has exactly nine top vertices, with profile

\[
1(1,1),\qquad2(1,2),\qquad2(2,1),\qquad4(2,2),
\]

where each pair is `(k⁻,k⁺)`. The existence or impossibility of
this no-full-entry case remains open. Sections 1–4 exclude the
one-sided full-entry case and its dual; §5 excludes the both-full
case.

## 1. Fiber witnesses and exactly one full entry

Assume the one-sided hypothesis. A full column of `K` makes every
vertex have exactly three top successors. Let
`P_t=Z∩Col(t)`, `C_t=Z∩Row(t)` for a top vertex `t`.
Thus `|P_t|=k⁻_t`, `|C_t|=k⁺_t`, and `k⁺_t∈{1,2}`.
The standard identities give

\[
BC=J_5,\quad K\le J_9,\quad
\sum k^- =\sum k^+=15,\quad \sum k^-k^+=25.
\]

For `F_uv=1`, the [packing witnesses](1485_boundary_central_defect.md)
are the `k⁻_u` distinct elements

\[
S_{u,v}=\{v*z:z\in P_u\}\subseteq TopSucc(v).
\]

They satisfy `(u*v)*b=v` for every `b∈S_{u,v}`. Equivalently,
`S_{u,v}=TopSucc(v)∩\{b:K_{b,u}=1\}`. A noncentral output
of `R_v` has at most two top inputs, since its size-three fiber
also contains a non-top sharp predecessor.

If `k⁻_v=2`, a witness fiber `R_b^{-1}(v)` has only one
noncentral slot. Consequently intersecting witness sets force equal
products, and a witness-intersection component cannot contain three
inputs. If `k⁻_v=1`, there are only two noncentral slots.

A full input `u` has three witnesses, exhausting `TopSucc(v)`.
It cannot occur in a missing column with `k⁻_v=2`: every other
missing input would have the same product, but that column has
`9−3k⁻_v=3` inputs.

For a full input and missing product `a=u*v`, the same argument
as in the [central-gap proof](1485_small_central_defects.md) gives

\[
(z*a)*v=a\qquad(z\in Z).
\]

Thus all top predecessors of `a` lie in its size-three `R_v`
fiber. The additional non-top sharp input leaves at most two.
Their central-predecessor weights sum to five, so they are exactly
the full input `u` and one input of weight two. These two inputs
are the whole top fiber. In particular distinct full inputs require
distinct weight-two partners.

In a missing column with `k⁻_v=1`, write its numbers of inputs
of weights three, two, one as `f,d,l`. The column size and the
weighted identity `(k⁻)ᵀF=5(3−k⁻)ᵀ` give

\[
(f,d,l)=(f,4-2f,2+f).
\]

Partner existence gives `f≤d`, hence `f≤1`.
If there are `a` full inputs, the first moment makes the number
of weight-one inputs `a+3`. Each full input has at least three
missing successors, all of weight one, and each such target accepts
at most one full input. Hence `3a≤a+3`, so `a=1`.
Denote the unique full input by `u`. Its missing row has three,
not six, entries, since there are only four weight-one vertices.
Therefore `k⁺_u=2`.

The complete central-degree profile is

\[
1(3,2),\quad2(2,1),\quad2(2,2),\quad
1(1,1),\quad3(1,2),                         \tag{1}
\]

where each pair is `(k⁻,k⁺)`. Indeed there are three entries
`k⁺=1`; their `k⁻` weights sum to five, and none is the full
vertex, so those weights are two, two, one.

## 2. Central labels and the partner alternatives

Put `P=P_u`, `Q=C_u`, of sizes three and two. Every weight-two
predecessor pair meets `Q` exactly once: full `u` has no missing
edge to a weight-two target. The three missing targets of `u`
are weight-one vertices whose singleton predecessor labels lie
outside `Q`; the fourth weight-one vertex has its label in `Q`.
Counting `B` incidences over the two central points of `Q` gives

\[
6=4+|P\cap Q|+1,
\]

so `|P∩Q|=1`. Name the central points so that

\[
P=\{p,a,c\},\quad Q=\{p,q\},\quad
Z\setminus P=\{q,b\},\quad O=Z\setminus Q=\{a,b,c\}.
                                                        \tag{2}
\]

In either central column indexed by `Q`, the full input contributes
weight three. The other two entries must have weight one and their
singleton predecessor labels must be `q,b`. Therefore the unique
weight-one vertex whose label lies in `Q` is labeled `q`; call it
`v_0`. It has `C_{v_0}=Q`. There is at least one missing target
of `u` labeled `b`.

Every weight-two top has its central-successor set contained in
`O`: the central columns in `Q` have already been seen to contain
only the full input and weight-one inputs.

Call a weight-two top a **partner** if its predecessor pair is
`{q,b}`. There is at least one partner. Indeed every noncentral
`u*v` has top predecessors `u,t`; their predecessor sets partition
`Z`, so `P_t=Z\setminus P`. For each such output,

\[
u*v=t*v.                                             \tag{3}
\]

There are at most two partners, since the central row `q` also
contains `v_0` and has three entries. Partners' `C` sets are
disjoint, because they have the same predecessor pair and `BC=J`.
Any two-element `C` set contained in `O` must contain `b`, since
its intersection with `P_u` has size at most one.

## 3. Exactly one partner is impossible

Let the unique partner be `t`. Equation (3) holds for all three
missing targets of `u`. Thus `C_t` avoids all their singleton
labels. At least one label is `b`. There are at most two labels
at `b`, since its central row also contains `t`; at any other
point in `O` there are at most two, since its central row contains
`u`. Hence there are exactly two distinct labels. Rename the
other label `a`; the omitted point is `c`. Then

\[
C_t=\{c\}.
\]

There are two multiplicity cases.

### 3.1. The missing labels are `a,a,b`

Central row degrees force the four weight-two predecessor pairs
to form a two-regular bipartite graph on `{p,q}` and `{b,c}`.
The doubled-edge alternative would give two `{q,b}` partners;
therefore the pairs are

\[
\{q,b\},\ \{p,b\},\ \{q,c\},\ \{p,c\}.
\]

The unique low input at `b` has successor set `Q`. Applying
`BC=J` successively in rows `q,b,p,c,a` gives the following
central-successor sets:

| Predecessor pair or singleton | Central-successor set |
| --- | --- |
| `{q,b}`, `{p,c}` | `{c}` |
| `{p,b}`, `{q,c}` | `{a,b}` |
| the two singleton-`a` tops | either `{c}`, `{a,b}` or `{a}`, `{b,c}` |

For the last row, `BC=J` requires a partition of `O`; the
two-element set must contain `b` by `K≤J` with `P_u`.
These are exactly the two displayed possibilities. Together with
`u,v_0` and the singleton-`b` top, whose successor sets are `Q`,
these are all tops.

First suppose the low pair has sets `{c}`, `{a,b}`. Every
three-top successor partition then includes a singleton-`{c}` cell.

For target `t`, the missing column consists of the `{q,b}` mid,
the `{p,c}` mid, and the singleton-`a` top with successor set
`{c}`. Its two weight-two inputs must have identical witness
sets: their two-element witness sets intersect, and their shared
output already fills the two-input top fiber; the remaining
singleton witness must avoid that output class. But the `{p,c}`
input witnesses the singleton-`{c}` cell and the `{q,b}` input
does not. This is a contradiction.

Now suppose instead that the low pair has sets `{a}`, `{b,c}`.
Every three-top successor partition has one of the two forms

\[
\mathrm{I}:Q,\{a\},\{b,c\};\qquad
\mathrm{II}:Q,\{c\},\{a,b\}.
\]

For a mid target with predecessor pair `{q,b}` or `{p,b}`,
the missing mid inputs have predecessor pairs `{q,b}`, `{p,c}`.
For a target with pair `{q,c}` or `{p,c}`, they have pairs
`{p,b}`, `{q,c}`. In both cases the third missing input is
the singleton-`a` top with successor set `{a}`. In type II,
the two mid witness sets differ: one selects `Q,{a,b}` and
the other selects `Q,{c}`. Thus all four mid rows must use
type I, and each contains the unique top whose successor set
is `{a}`. But the two mid rows with predecessor pairs `{p,b}`
and `{p,c}` must be disjoint by `BD=J` at central point `p`.
This is a contradiction in the second orientation as well.

### 3.2. The missing labels are `a,b,b`

The remaining predecessor pairs, besides `{q,b}`, are either

\[
\{p,a\},\{p,c\},\{q,c\},
\quad\text{or}\quad
\{p,c\},\{p,c\},\{q,a\}.                    \tag{4}
\]

This follows by filling residual degrees `2,1,2,1` on
`p,a,c,q`; all pairs cross `Q` and `O`.
The two singleton-`b` tops have two-element successor sets
partitioning `{p,a,q,b}`. Their only possibilities, using
`K≤J`, are the pairings `Q,{a,b}` or `{p,b},{q,a}`.
The singleton-`a` top has successor set `{c}`. Both `b` tops
and `v_0` have weight two, so (1) makes it the unique weight-one
low top. In either case of (4), central row `q`, containing
`v_0`, `t`, and the remaining `q`-mid, makes that mid's
successor set `{a,b}`. In the path case, rows `c,p,a` then
successively force `{c}`, `{a,b}`, `{c}` for the other mids
and the singleton-`a` top. In the doubled-`{p,c}` case,
row `a` immediately forces the latter's set to be `{c}`.

In the first case of (4), `BC=J` forces the `{p,c}` mid to
have successor set `{c}`, and the other two mids to have set
`{a,b}`. All singleton successor cells are again `{c}`, so
the target-`{q,b}` contradiction from §3.1 applies unchanged.

In the second case of (4), the `{q,a}` mid has successor set
`{a,b}`, while the two `{p,c}` mids have disjoint successor
sets partitioning `O`. One is a singleton `a` or `c`; the
other is the complementary pair containing `b`. The pairing
`{p,b},{q,a}` for the low `b` tops is forbidden by the
predecessor pair `{q,a}`, so their sets are `Q,{a,b}`.

Fix either target with predecessor pair `{p,c}`. Its missing
column consists of the `{q,a}` mid, the unique `{p,c}` mid
whose successor set avoids `c`, and the low `b` top with
successor set `{a,b}`. Every successor partition consists of
`Q`, a singleton `a` or `c`, and its complement in `O`.
The two mid witnesses both include `Q`, but their other witnesses
are the distinct cells containing `a` and `c`. Thus they cannot
be identical, again contradicting the size-two top-fiber bound.

## 4. Exactly two partners: the two incidence shapes

Now there are two partners with predecessor pair `{q,b}`.
Their successor sets partition `O`, with sizes one and two,
because central row `q` consists of them and `v_0`.
Central row `b` then has one remaining top with successor set
`Q`; it is a singleton-`b` top. Thus exactly one missing target
of `u` is labeled `b`, and the other two labels are `a,c`,
possibly equal. The remaining two weight-two tops have predecessor
pairs containing `p`.

### 4.1. Repeated labels `a,a,b`

The remaining two mids both have predecessor pair `{p,c}`.
Each of the following pairs of tops has central-successor sets
partitioning `O` into a singleton and a pair:

\[
\text{the two }\{q,b\}\text{ mids},\qquad
\text{the two }\{p,c\}\text{ mids},\qquad
\text{the two singleton-}a\text{ tops}.
\]

The partition has one of two types:

\[
\mathrm{I}:\ Q,\{a\},\{b,c\};\qquad
\mathrm{II}:\ Q,\{c\},\{a,b\}.                \tag{5}
\]

Every mid target has a missing column consisting of one `{q,b}`
mid, one `{p,c}` mid, and one singleton-`a` low top. Their two
mid witness sets must coincide, which forces its ordinary top
successor partition to be type I.

Conversely, either singleton-`a` target, and the singleton-`b`
target, must have type II. Its missing column contains full `u`,
one partner, the other mid of type `{p,c}`, and three low inputs
with labels `q,b,a`. The full output occupies one noncentral
slot at every witness. In type I, the other mid witnesses both
`Q` and `{b,c}`; the low inputs labeled `q,b` witness those
two cells respectively. They would all share the remaining slot,
giving a forbidden three-input output fiber.

Let `i,j` be the numbers of available singleton-`a` and
singleton-`c` successor cells. There are only three singleton
successor sets, so `i+j=3`. The two `{p,c}` mid rows are
disjoint by `BD=J` at central point `p`; both have type I,
so `i≥2`. The two singleton-`a` rows are disjoint by `BD=J`
at point `a`; both have type II, so `j≥2`. This contradicts
`i+j=3`.

### 4.2. Distinct labels `a,b,c`

The two remaining mids have predecessor pairs `{p,a}` and
`{p,c}`. All three central-successor singletons are `a` or
`c`, and every successor pair in `O` contains `b`; this follows
from (1), `BC=J`, and `K≤J` as above. Thus every ordinary top
successor partition has one of the two types in (5).

Use target `v_0`, whose predecessor label is `q`. Its six
missing inputs are all four mids and the singleton-`a` and
singleton-`c` tops. All four mids witness the `Q` cell. That
cell's fiber has only two noncentral slots, and each output has
at most two top inputs. The four mids therefore occupy exactly
two full two-input output classes.

Write the singleton cell of the chosen partition as `{z}`, where
`z` is `a` or `c`, and let `z'` be the other point. The pair
cell is `{b,z'}`. Three mids witness this cell: both partners
`{q,b}` and the mid `{p,z'}`. Thus both already-full output
classes occur at this cell. But the missing singleton-`z'`
input witnesses that same cell and would have to join one of
those classes, producing three top inputs. This is impossible.

Both partner counts and every incidence shape have been excluded.
This proves the one-sided-full exclusion; applying the dual argument
also excludes a full `k⁺` entry without any full `k⁻` entry.

## 5. Full entries in both directions are impossible

Suppose now that both vectors have a full entry. The all-one row
and column of `K` make every vertex have three top predecessors
and three top successors. The
[full-support coincidence lemma](1485_small_central_defects.md)
therefore applies: `k⁻_t=3` if and only if `k⁺_t=3`.

Let `f≥1` be the number of these common full vertices, and put
`ε⁻=3−k⁻`, `ε⁺=3−k⁺`. Their common positive support has
size `9−f`. The incidence moments give

\[
\sum\varepsilon^-=\sum\varepsilon^+=12,
\qquad\sum\varepsilon^-\varepsilon^+=16.
\]

There are `3+f` twos in each defect vector. If `t` positions
have a two in both vectors, expansion on the common support gives

\[
16=(9-f)+2(3+f)+t=15+f+t.
\]

Hence `f=1`, `t=0`. There is one top `w` with profile `(3,3)`,
four tops with profile `(1,2)`, called horizontal tops, and four
with profile `(2,1)`, called vertical tops.

### 5.1. The two possible incidence patterns

The predecessor and successor triples of `w` intersect in exactly
one point: they are triples in a five-element set, and `K≤J`
allows intersection at most one. Label them

\[
P_w=\{0,1,2\},\qquad C_w=\{0,3,4\}.
\]

Central rows `0,1,2` contain `w` and two vertical tops: their
remaining central-successor weights must sum to two. Rows `3,4`
contain two horizontal tops and one vertical top. Dually, central
columns `1,2` contain two vertical tops and one horizontal top;
columns `0,3,4` contain `w` and two horizontal tops.

Thus the horizontal tops have singleton predecessor labels `3,3,4,4`,
and the vertical tops have singleton successor labels `1,1,2,2`.
The horizontal cells in the two-by-two rectangle of rows `3,4`
and columns `1,2` form a permutation. Relabel so that they are
`(3,1)` and `(4,2)`.

The two horizontal successor pairs in each row are disjoint. Each
pair meets `P_w` at most once. The two vertical predecessor pairs
in each column are likewise disjoint and each meets `C_w` at most
once. Consequently the four binary choices are exactly:

| Group | Choice 0 | Choice 1 |
| --- | --- | --- |
| Horizontal tops with predecessor `3`: successor pairs | `03,14` | `04,13` |
| Horizontal tops with predecessor `4`: successor pairs | `03,24` | `04,23` |
| Vertical tops with successor `1`: predecessor pairs | `01,24` | `02,14` |
| Vertical tops with successor `2`: predecessor pairs | `01,23` | `02,13` |

Here `ij` denotes the unordered pair `{i,j}`. A horizontal
successor pair cannot equal a vertical predecessor pair, because
that would give an entry two in `K`. These restrictions leave
exactly two patterns. Indeed, if the first choice is zero, the
third cannot be one (common pair `14`), the second must be one
(otherwise common pair `24`), and the fourth must be one
(otherwise common pair `23`). If the first choice is one, the
fourth must be zero (common pair `13`), the second must be zero
(common pair `23`), and the third must be one (common pair `24`).
The two patterns are therefore

\[
(0,1,0,1),\qquad(1,0,1,0).                     \tag{6}
\]

This is a four-choice deduction, not an unreported enumeration.

### 5.2. A singleton witness excludes both patterns

In the first pattern, choose the vertical target with predecessor
pair `01` and successor singleton `1`. Its missing inputs are
the horizontal top with predecessor `4` and successor pair `23`,
and the two vertical tops with successor singleton `2`. Those
two vertical inputs have predecessor pairs `02` and `13`.

In the second pattern, choose the vertical target with predecessor
pair `02` and successor singleton `1`. Its missing inputs have
predecessor sets `3`, `02`, and `14`; the last two are vertical
inputs with successor singleton `1`.

In either case the target has central in-degree two, and there are
three missing inputs of weights one, two, two. The two mid inputs
have two-element witness sets inside the target's three top
successors. These sets intersect, so they give the same noncentral
output. If their witness sets differed, their union would be all
three successors, and the remaining low input's nonempty witness
would force it into the same already-full two-input top fiber.
Thus the two mid witness sets must be identical.

But the three top successors partition the five central points by
their `C` sets. At least one of those sets is a singleton, since
otherwise their total size would be at least six. The only singleton
successor sets are `{1}` and `{2}`. In the first pattern each
of these singletons belongs to exactly one of `02,13`; in the
second, each belongs to exactly one of `02,14`. Its top vertex
therefore witnesses one mid input and not the other. Their witness
sets cannot be identical, a contradiction in both patterns.

This excludes the both-full case.

## 6. The remaining no-full profile

The ten-top theorem and its incidence corollary first force `|T|=9`
whenever `r=3` and `|Z|=5`. The preceding sections exclude a full
entry on either side. All central degrees are consequently one or
two. Each vector has six twos, since its sum is fifteen over nine
positions. The mixed moment twenty-five makes the two supports of
twos intersect in four positions. The exact remaining profile is

\[
\boxed{1(1,1),\quad2(1,2),\quad2(2,1),\quad4(2,2).}
\]

This is a necessary profile, not a model construction or an exclusion
of five central vertices. The no-full-entry case remains unresolved.
