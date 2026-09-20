# Three partition labels for degree-six top profiles

Research note, 19 September 2026. This gives analytic reductions for
minimum degree four, four central vertices, and least noncentral
degree six. It does not exclude this configuration.

Label the central set by `[4]` and the tops by `t_ij=z_i*z_j`.
For each degree-six vertex `a`, the
[minimal-central-count theorem](1485_minimal_central_count.md)
writes

\[
TopPred(a)=\{t_{i,\alpha_a(i)}:i\in[4]\},\qquad
TopSucc(a)=\{t_{\beta_a(j),j}:j\in[4]\}.
\]

The maps `α_a,β_a` have the same two-element image `S_a`, and
each value occurs twice. Let `s_a` be the partition
`{S_a,S_aᶜ}` of `[4]` into two pairs. Let `p_a,w_a` be the
kernel partitions of `α_a,β_a`. All three labels belong to the
same three-element set of pair partitions.

## 1. Unique intersection has a simple three-label criterion

For any degree-six vertices `a,c`,

\[
\boxed{|TopSucc(a)\cap TopPred(c)|=1
       \quad\Longleftrightarrow\quad
       s_a=p_c\ \text{or}\ s_c=w_a.}                       \tag{1}
\]

Indeed, the intersection counts the fixed points of
`β_a∘α_c` on `S_a`. If `α_c` is constant on `S_a`, or
`β_a` is constant on `S_c`, this composite is constant on a
two-element set and has exactly one fixed point. These two
conditions are respectively `s_a=p_c` and `s_c=w_a`.
If neither holds, the two restrictions are bijections between the
two-element sets. Their composite is a permutation, with zero or
two fixed points, not one.

In the four-degree order-48 setting, a pair failing (1) must have
a sharp middle in the degree-eight class `B`. A central middle
is impossible, and otherwise the only available middle class would
be top; the unique-minimum-middle theorem would then require
exactly one top middle.

In particular, at the remaining `|A|=|B|=14`, all-sharp-count-two
profile, at most four selected degree-six profiles in every row
and column can fail (1). There are exactly four sharp two-step
paths through `B` in either direction at every member of `A`.
This is only a necessary restriction: having exactly one top middle
does not prevent a lower-degree sharp middle from also existing.

## 2. A fixed support has at most four vertices

Fix an actual two-element support `S`, rather than merely the
partition `{S,Sᶜ}`. For two degree-six vertices with this support,
their good ordered top pairs are disjoint exactly when

\[
\alpha_c=\overline{\alpha_a}
\quad\text{or}\quad
\beta_c=\overline{\beta_a},                                 \tag{2}
\]

where the bar interchanges the two values in `S`.

To see this, their common good pairs are counted by
`A₀B₁+A₁B₀`, where `A_i` is the number of positions at which
the two `α` maps agree on value `i∈S`, and `B_i` is the
analogous count for the `β` maps. Two balanced maps to `S`
are identical, complementary, or agree once on each value.
Unless the `α` maps are complementary, both `A_i` are positive;
then disjointness requires both `B_i=0`, which is precisely
complementarity of the `β` maps. The converse is immediate.

Any family satisfying (2) has all its `α` maps in one
complementary pair, or all its `β` maps in one complementary
pair. For if two `α` maps belong to different complementary
pairs, their `β` maps must be complementary. Any further `β`
map outside that pair would require its `α` map to be
complementary to both of the original, distinct `α` maps,
which is impossible.

On the side with a common complementary pair, each of its two
maps can occur at most twice: with that map fixed, the opposite
maps in (2) must themselves be complementary. Consequently

\[
\boxed{|\{a:S_a=S\}|\le4.}                                 \tag{3}
\]

At equality there are two occurrences of each map on the fixed
side. On the other side the two opposite maps form a complementary
pair for each occurrence class; those two pairs need not be the
same. Thus equality does **not** force a single four-profile grid.

There are six actual supports, giving at most 24 degree-six
vertices, and at most eight with any one partition label `s_a`.
The first bound agrees with the earlier global top-pair count.
The local structure and criterion (1), rather than a stronger
cardinality conclusion, are the additional information here.
