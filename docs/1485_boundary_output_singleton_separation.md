# Uniform singleton-label separation at the boundary first-output degree

Research note, 20 September 2026. This is an analytic finite E1485
theorem. It uses neither enumeration nor a Lean declaration.

Let the minimum translation degree be `r≥3`. Let `Z,T` be the central
and top classes, and put `m=|Z|`. Suppose the least degree of a
noncentral **product of two tops** is `p=2r−1`. Write

`P_v=Col(v)∩Z`, `C_v=Row(v)∩Z`

for top central blocks, and let `S_P,S_C` be the labels occurring as
singleton predecessor and successor blocks.

**Theorem.**

\[
\boxed{S_P\cap S_C=\varnothing.}
\]

There is **no central-count restriction**. In particular this replaces
the finite overlap exclusions formerly used at `r=4,m=p=7`, and also
applies to the remaining eight-, nine-, and ten-central cases.

## 1. Exact replacement for arbitrary omissions

Take a singleton source `u` with `C_u={c}`. For any `d∈Row(c)`,
choose `z∈C_d` and a least noncentral member `a` of `u*Col(z)`.
The local degree bound and global minimality of `p` force `d(a)=p`.
The exact-replacement identity is

\[
Row(a)=L_u^{-1}(a)\ \sqcup\bigl(Row(c)\setminus\{d\}\bigr).
\tag{1}
\]

Its [fiber proof](1485_maximal_central_block_first_output_gap.md#2-every-omitted-central-row-point-occurs)
requires the singleton source and equality `p=2r−1`, but **not**
a singleton omission or a maximal predecessor block. Those extra
conditions were used there to conclude a crown; identity (1) does
not require that conclusion.

By the [first-output theorem](1485_first_top_output_fibers.md), the top
profiles `U=TopPred(a)` and `V=TopSucc(a)` have a common size `t`,
with

\[
r\le t\le 2r-2.
\tag{2}
\]

Their central-middle matrix `K_(x,y)=|C_x∩P_y|` has every row and
column sum `r−1`. The lower bound in (2) follows from at most `r−1`
non-top neighbors; the upper bound follows from at least one non-top
neighbor. The predecessor blocks of `U` and successor blocks of `V`
each partition `Z`.

The profile `V` retains all `r−1` tops of `Row(c)\{d}`. Its new
tops lie outside `Row(c)`, and their nonempty successor blocks partition
exactly `C_d`.

## 2. A common label forces a large isolated complete block

Suppose `c∈S_P∩S_C`, choose a singleton source `u` as above, and
take any top `v` with `P_v={c}`. For each omission `d≠v` in
`Row(c)`, identity (1) retains `v` in `V`.

The column at `v` has an entry one precisely at those rows `x∈U`
whose successor block contains `c`. Its column sum gives exactly
`r−1` such rows. Each of these rows has entries one at all the
`r−1` retained columns, since all their predecessor blocks contain
`c`. This already exhausts each row's degree `r−1`. It also exhausts
the degree of each retained column. Thus these rows and columns form
an **isolated complete bipartite block** `K_(r−1,r−1)`.

The complementary rows and columns are nonempty because `t≥r`.
They still have degree `r−1`, entirely within that complementary
block. Therefore `t−(r−1)≥r−1`. Combining with (2) gives

`t=2r−2`.

There are consequently exactly `r−1` new tops in `V`. Their nonempty
successor blocks partition `C_d`, so `|C_d|≥r−1`. This holds for
**every** one of the `r−1` omissions `d≠v`. The central partition
on `Row(c)` therefore gives

\[
\boxed{m\ge(r-1)^2+|C_v|\ge(r-1)^2+1.}
\tag{3}
\]

By itself this already separates singleton labels whenever
`m<(r−1)²+1`. The equality case can also be excluded analytically.

## 3. The only possible central count is the equality case

The [full-size block theorem](1485_full_central_blocks_boundary_output.md)
does not assume singleton separation. Since both singleton-label
sets are nonempty, it gives

`|P_w|,|C_w|≤r−1` for every top `w`.

A central partition containing a singleton thus has size at most
`1+(r−1)(r−1)`. Combining with (3), put

\[
m=M:=(r-1)^2+1.
\tag{4}
\]

Every central partition has **at most one singleton block**: two
singletons and `r−2` blocks of size at most `r−1` would cover at
most `2+(r−2)(r−1)<M`, since `r≥3`.

For any common singleton label `c`, inequality (3) applies to every
top `v` with `P_v={c}`. Equality (4) forces `|C_v|=1`, and the
other `r−1` successor blocks on `Row(c)` all have size `r−1`.
The dual argument forces `|P_u|=1` for **every** top `u` with
`C_u={c}`.

Both singleton tops at a common label are globally unique. Two tops
with predecessor `{c}` would give two singleton successor blocks
on `Row(c)`; two tops with successor `{c}` would give two singleton
predecessor blocks on `Col(c)`. Both contradict the preceding
one-singleton bound. Write these unique tops as

\[
(P_{u_c},C_{u_c})=(\{y(c)\},\{c\}),\qquad
(P_{v_c},C_{v_c})=(\{c\},\{z(c)\}).
\tag{5}
\]

## 4. Almost every label must be singleton on each side

Return to an arbitrary omission `d≠v_c` on `Row(c)`. Its successor
block has size exactly `r−1`, and Section 2 supplies exactly `r−1`
new tops whose nonempty successor blocks partition it. Every one of
these new blocks must be singleton.

The union of the omitted blocks as `d≠v_c` varies is
`Z\{z(c)}`. Consequently

\[
S_C\supseteq Z\setminus\{z(c)\}.
\]

The dual argument gives `S_P⊇Z\{y(c)}`. For `I=S_P∩S_C`,
these two inclusions imply

\[
|I|\ge m-2\ge3,
\tag{6}
\]

since `r≥3` makes `m=(r−1)²+1≥5`.

## 5. The outside singleton map gives the contradiction

Now omit `v_c` itself from `Row(c)`. Its successor block is the
singleton `{z(c)}`. Exact replacement provides at least one new top;
its nonempty successor blocks partition that singleton, so there is
exactly one, say `w`, with `C_w={z(c)}`. The tops `v_c,w` are
distinct. If `z(c)` were in `S_P`, it would be a common label with
two singleton-successor tops, contradicting Section 3. Hence

`z(c)∈S_C\S_P`.

The dual omission of `u_c` gives `y(c)∈S_P\S_C`.

The map `c↦y(c)` from `I` to `Z\S_C` is injective: different
common labels give different singleton-successor tops `u_c`, and
two with the same predecessor singleton `{y}` would put two singleton
successor blocks on `Row(y)`. But Section 4 says that `Z\S_C`
has at most one label. Thus `|I|≤1`, contradicting (6).

This proves uniform singleton-label separation.

## Proof dependencies and the seven-central consequence

The proof uses only central-endpoint partitions and orthogonality,
the first-output fiber theorem, arbitrary-omission exact replacement,
and the analytic full-size block theorem. None uses singleton-label
separation, so there is no circular dependence on an older overlap
result or finite check.

The [seven-central degree-seven exclusion](1485_seven_central_three_by_two.md)
now needs only **three finite lemmas**: its `(3,3)`, `(3,1)`, and
`(3,2)` profile exclusions. All earlier common-singleton-overlap
checks remain valid independent corroboration, but are no longer
mathematical dependencies of that proof.
