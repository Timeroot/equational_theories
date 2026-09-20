# Eighteen tops cannot have two small degree-five profiles

Proof, 20 September 2026. The mathematical argument has been
independently audited. One pure central subcase invokes the existing
audited 200-fixture lemma; no new enumeration or SAT premise is used.
This is not a Lean formalization.

Assume order forty, minimum degree four, eight central elements,
and eighteen tops. Let `q` count degree-five elements with three
top predecessors and successors. **Then `q≠2`.** Together with
the [preceding bound](1485_order_forty_eight_central_eighteen_small_profile_bound.md),
this proves `q≤1`, independently of the total degree-five count `a`.

## 1. Two distinct profiles cannot share a nontrivial central rectangle

For a small degree-five element `a`, write `U_a,V_a` for its
three-element top predecessor and successor sets. The blocks
`P_(U_a),C_(V_a)` partition the eight central labels with pattern
`332`. Their central matrix

\[
                   K_{uv}=|C_u\cap P_v|
                 \qquad(u\in U_a,\ v\in V_a)
\]

is a permutation matrix. Every zero of this matrix is a top-input
pair whose product is `a`; see the
[first-output profile theorem](1485_first_successor_degree_profiles.md).

If `a≠b`, every entry of
`(U_a∩U_b)×(V_a∩V_b)` must therefore be central: otherwise one
ordered pair would have both products `a` and `b`. A permutation
matrix cannot contain an all-one rectangle of shape `2×1` or
`1×2`. Consequently, if both intersections are nonempty, both
have size one.

Use `γ_u` for the number of small degree-five successors of a top
and `δ_u` for its small degree-five predecessors. We will repeatedly
use the following established restrictions:

\[
\begin{array}{ll}
 P_u=1\Longrightarrow\gamma_u=0,
   &C_u=1\Longrightarrow\delta_u=0,\\
 C_u=3\Longrightarrow\gamma_u=0,
   &P_u=3\Longrightarrow\delta_u=0.
\end{array}
 \tag{1}
\]

The first line is the profile partition `332`; the second is the
[unused-top upper bound](1485_first_degree_source_unused_tops.md#2-a-maximal-central-source-cannot-leave-no-unused-top).
For every central row and column, the profile partition identities give

\[
                \sum_{u\in Row(z)}\gamma_u=q,
                \qquad\sum_{u\in Col(z)}\delta_u=q.
 \tag{2}
\]

## 2. Exactly two paired central inventories survive

Suppose `q=2`. Retain the notation from the preceding bound:

\[
 u=n_{12},\quad v=n_{21},\quad z=n_{13},\quad w=n_{31},
 \quad t=n_{33},\quad U=u+2z,\quad V=v+2w.
\]

Its central moment identities and small-profile capacity inequalities
give

\[
\begin{gathered}
 n_{11}=8+z+w-t,\quad n_{32}=4+U-2t,\quad
 n_{23}=4+V-2t,\quad n_{22}=2-2U-2V+4t,\\
 t\ge U+w,V+z,\qquad
 2u+4z+w\le4,\quad2v+4w+z\le4.
\end{gathered}
 \tag{3}
\]

The two small predecessor profiles have four maximal-block
incidences in total. By (1), the only eligible maximal tops are
types `31,32`. Each top occurs in at most two profiles. The dual
eligible maximal types are `13,23`.

If `z>0`, (3) forces `z=1,w=u=0,v≤1`. Since `t≥2` and
at least two `32` tops are needed, `n32=6−2t≥2`, so `t=2`.
The successor profiles need at least two eligible maximal tops,
so `n13+n23=1+v≥2`, giving `v=1`. There are now just two
eligible maximal tops in each direction. Both belong to both
respective profiles, contradicting §1. The dual excludes `w>0`.

Thus `z=w=0`, `u,v≤2`. In each direction at least two eligible
maximal tops are required. Therefore

\[
              t\ge u,v,\qquad2t\le2+u,2+v.
\]

The complete possibilities are

- `t=0,u=v=0`;
- `t=1,u,v∈{0,1}`;
- `t=2,u=v=2`.

Except for `t=1,u=v=1`, each positive-`t` possibility has one
eligible maximal family of size two and the other of size at most
three. The two profiles then share both maximal tops in one
direction and at least one maximal top in the other, again contrary
to §1. The only remaining matrices, with rows indexed by `P=1,2,3`
and columns by `C=1,2,3`, are

\[
 \begin{pmatrix}8&0&0\\0&2&4\\0&4&0\end{pmatrix},
 \qquad
 \begin{pmatrix}7&1&0\\1&2&3\\0&3&1\end{pmatrix}.
 \tag{4}
\]

## 3. The pure inventory is the already excluded central grid

In the first matrix every singleton block is paired with a singleton.
A central row of pattern `3311` has two triple-`C` tops and two
unit tops. Every one has `γ=0` by (1), contradicting (2).

There are eight unit tops, each contributing one singleton occurrence
to the eight central rows. With `3311` excluded, the possible
patterns `3221,2222` force every row to be `3221`. The dual gives
the same column patterns.

Both maximal-block families have size four. The
[one-hole theorem](1485_one_hole_first_output_grid.md) supplies their
intersection and deficiency conditions. Hence the
[common finite central-profile lemma](1485_order_forty_eight_central_eighteen_two_small.md#common-finite-central-profile-lemma)
applies: none of its 200 exhaustive central fixtures admits even one
small profile. This excludes the first matrix.

## 4. A repeated retained triple excludes the mixed inventory

Consider the second matrix. The two small predecessor profiles each
choose two of the three type-`32` tops. These pairs must be distinct:
if they were equal, §1 would require disjoint successor profiles,
but two two-subsets of the three type-`23` tops intersect. Thus
the predecessor profiles have a common type-`32` top `s`; dually
the successor profiles have a common type-`23` top `v`.

By §1 the common entry `(s,v)` is central. Since each profile's
central matrix is a permutation, `v` is the unique retained top
at the source `s` in both profiles.

Apply the
[unused-top identity](1485_first_degree_source_unused_tops.md#1-removing-any-selected-collection-of-first-degree-outputs)
to these two small successors of `s`. Here `|C_s|=2`, and both
retained blocks are the same triple `C_v`. The unused top set `W`
therefore satisfies

\[
 |W|=18-4\cdot2-2(3-1)=6,
 \qquad
 \sum_{w\in W}|C_w|=2|C_v|=6,
 \tag{5}
\]

and its exact successor-block multiplicity is

\[
              \sum_{w\in W}\mathbf1_{x\in C_w}
                     =2\mathbf1_{x\in C_v}.
 \tag{6}
\]

All six unused blocks are consequently singletons, two at each of
the three labels in `C_v`. The mixed inventory has only one
nonunit top with singleton `C`, namely its type-`21` top. Thus
at least one of these three labels has two distinct unused *unit*
tops with that same successor singleton.

The central column at this label contains the two unit tops. Its
four predecessor blocks partition eight labels, so its other two
blocks both have size three: the column has pattern `3311`.
The units have `δ=0` by their singleton `C`; the other two tops
have `δ=0` by their triple `P`, using (1). This contradicts the
column identity (2), whose sum must be two. The second matrix is
also impossible, completing the exclusion of `q=2`.
