# Four central vertices forbid full central incidence at minimum degree three

Research note, 18 September 2026. This is an analytic finite proof,
independent of the total order and not yet a Lean declaration.

**Theorem.** In a finite E1485 magma with minimum translation degree
three and exactly four central vertices, every top vertex has central
in-degree and central out-degree at most two.

In fact the central-incidence identities alone prove the assertion;
no additional multiplication or degree-descent argument is needed.
Together with the [eight-top exclusion](1485_four_central_eight_top.md),
the theorem removes both that top count and every full-entry case.
It does not exclude the remaining no-full-entry cases.

## 1. A full entry determines the degree profile

Let `Z,T` be the central and top sets, with `|Z|=4`. Write
`B:Z→T`, `C:T→Z` for the zero-one central-incidence matrices,
and put

\[
 K=CB,\quad F=J-K,\quad k^-=B^T\mathbf1,\quad
 k^+=C\mathbf1.
\]

Their standard properties are

\[
 BC=J_4,\qquad 0\le K\le J,
\]

with every row of `B` and column of `C` having sum three, and
all entries of `k⁻,k⁺` positive and at most three.

Suppose that `k⁻` has a full entry, equal to three. Then
`|T|=9`, by the [full-entry support argument](1485_small_central_defects.md).
Explicitly,

\[
 BF=\mathbf1(3-k^-)^T.
\]

The corresponding column of `BF` is zero. Every column of `B`
has a positive entry, so that column of `F` is zero. The same
column of `K` has sum `3k⁻=9`, and hence has exactly nine
entries.

The degree moments are now

\[
 \sum_T k^-=\sum_T k^+=12,
 \qquad \sum_T k^-k^+=16.                 \tag{1}
\]

There are exactly one top vertex `U` with central in-degree
three, one `M` with central in-degree two, and seven `L` vertices
with central in-degree one. Indeed the excess of the nine positive
in-degrees over nine is only three.

Subtracting `Σk⁺=12` from the mixed moment in (1) gives

\[
 2k^+_U+k^+_M=4.
\]

Positivity forces

\[
 k^+_U=1,\qquad k^+_M=2.                 \tag{2}
\]

This conclusion does not assume that the out-degrees have no full
entry. Thus the proof handles one-sided and both-sided full entries
at once.

## 2. A missing low column cannot contain both exceptional inputs

For a low vertex `v`, with `k⁻_v=1`, column `v` of `F` has
exactly six ones, since the same column of `K` has sum three.
Their total central in-degree weight is eight:

\[
 \sum_{t:F_{tv}=1} k^-_t=8.              \tag{3}
\]

For completeness, the general identity behind this is

\[
 (k^-)^TF=4(3-k^-)^T,
\]

which follows from `BC=J₄` and `Σk⁻=12`.

If the six inputs in (3) included both `U` and `M`, their
weight would be at least `3+2+4=9`. Consequently

\[
 F_{Uv}=1\quad\Longrightarrow\quad K_{Mv}=1
 \qquad(v\text{ low}).                  \tag{4}
\]

## 3. Three required central successors do not fit in a pair

By (2), the central successor set of `U` is a singleton `{q}`,
whereas that of `M` has size two.

Fix any central vertex `z≠q`. The row of `B` indexed by `z`
has three entries. At most two of these can be `U` and `M`,
so at least one is a low vertex `v`. Its singleton central
predecessor set is exactly `{z}`.

There is no central middle from `U` to `v`, because
`{q}∩{z}=∅`. Thus `F_{Uv}=1`, and (4) gives `K_{Mv}=1`.
The latter says exactly that `z` is a central successor of `M`.

All three vertices of `Z\{q}` must therefore be central
successors of `M`, contradicting its central out-degree two.
No full central in-degree exists. Apply the dual argument to
exclude full central out-degrees. This proves the theorem.

## 4. The two remaining top counts and their exact profiles

Let `h=|T|`, and let `n_ij` count top vertices with central
in/out profile `(i,j)`. All entries are now one or two. Expanding
the same three moments gives

\[
n_{22}=h-8,\qquad n_{12}=n_{21}=20-2h,
\qquad n_{11}=4h-32.
\]

Nonnegativity forces `8≤h≤10`. The separate eight-top theorem
excludes the lower endpoint, leaving exactly these possibilities:

| Top count | Central in/out profiles |
| ---: | --- |
| 9 | `4(1,1), 2(1,2), 2(2,1), 1(2,2)` |
| 10 | `8(1,1), 2(2,2)` |

These profiles are necessary conditions only. Neither remaining case
is excluded by this note.
