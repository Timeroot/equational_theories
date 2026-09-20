# Three central vertices cannot have exactly two degree-four vertices

Research note, 19 September 2026. This proof uses an explicit finite
top-profile check, not SAT, an ATP, or magma enumeration. It is not
yet formalized in Lean.

**Theorem.** In a finite E1485 magma with minimum degree three and
exactly three central vertices, the degree-four class has at least
three vertices.

The [singleton case](1485_three_central_singleton_exclusion.md) is
excluded analytically. Here we exclude a two-element degree-four
class `A={a,b}` without imposing restrictions on its reciprocal
class or on the other degree classes.

## The finite objects

As usual, write `t_ij` for the nine top vertices. Every vertex has
three top predecessors and successors. Set

\[
K=\{(t_{ij},t_{kl}):j=k\}.
\]

A degree-four vertex has top profiles

\[
U_f=\{t_{i,f(i)}:i<3\},\qquad
V_g=\{t_{g(j),j}:j<3\},
\]

where both `f,g` are permutations. Its good top pairs are the six
pairs `(U_f×V_g)\K`. There are 36 possible profiles, with distinct
good sets. Two actual vertices have disjoint good sets. There are
414 unordered disjoint pairs of such profiles. Let `G_A` denote
the resulting twelve degree-four pairs.

For a degree-five vertex `x`, its top profiles `U,V` have the same
form but with arbitrary functions on three labels, giving 729
possible profile pairs. Strict descent at a bad middle gives

\[
G_x=(U\times V)\setminus(K\cup G_A).              \tag{1}
\]

Every row and column has one or two good entries: a three-element
top translation fiber must contain a top input, since `x` has
only two non-top neighbors, and must contain a sharp non-top input.

Also `|G_x|≤4`. If `x` has two sharp successors, its three top
fibers have only one remaining slot each, giving `|G_x|≤3`.
Otherwise it has one sharp and one non-sharp non-top successor.
That successor has complementary degree four, so the
[slot bound](1485_three_central_minimum_top_output.md#a-general-top-fiber-slot-bound)
places it in at least two of the top fibers; hence `|G_x|≤6−2=4`.

## Companion outputs must have degree four

If a row of `G_x` at `u=t_ij` has two good entries, the
[companion argument](1485_three_central_singleton_exclusion.md#3-a-two-entry-good-row-forces-degree-four-companion-outputs)
applies to each good input `v=t_kl`. Its other noncentral
companion input is `t_hl`, where `{h}={0,1,2}\{j,k}`. The
product at that companion must have degree four. Consequently

\[
(u,t_{hl})\in G_A.                               \tag{2}
\]

Dually, if the column at `v=t_kl` has two good entries, then

\[
(t_{ih},v)\in G_A.                               \tag{3}
\]

For clarity, this argument does not require the degree-four output
to be unique. The fiber `L_u⁻¹(x)` contains two good top inputs
but `x` has two non-top successors. One of those successors must
map to the other noncentral member of `u*Col(z_l)`, and strict
descent makes its degree four. That is all (2) uses.

## Even all possible degree-five profiles leave uncovered triples

For each of the 414 possibilities for `G_A`, collect **all**
degree-five candidates satisfying (1), the row/column counts,
`|G_x|≤4`, and (2)–(3). Write `L` for the union of `G_A` and
all their good sets. It overestimates the possible pairs of degree
four or five; candidates need not coexist or have disjoint good sets.

The [central-column triple lemma](1485_three_central_singleton_exclusion.md#1-each-central-column-triple-contains-a-degree-four-or-degree-five-output)
requires that, for every top `u=t_ij` and central-column label `l`,
at least one of the two noncentral pairs

\[
\{(u,t_{kl}):k\ne j\}
\]

have degree four or five. The dual condition holds for fixed right
endpoint and fixed left grid row.

The finite check finds that `L` misses at least twelve of these
54 required pairs of positions, for every degree-four profile pair.
Thus actual top products cannot satisfy the triple lemma.

Run the complete check with

```text
python3 scripts/1485_m3_two_degree_four_check.py
```

Its exact inventory is:

| Degree-five candidates | Their good-pair union | Missed triples, including duals | Degree-four profile pairs |
| ---: | ---: | ---: | ---: |
| 0 | 0 | 30 | 36 |
| 0 | 0 | 33 | 72 |
| 4 | 10 | 19 | 216 |
| 6 | 10 | 20 | 54 |
| 18 | 24 | 12 | 36 |

These counts use all 414 disjoint pairs directly, without a symmetry
quotient. No assumptions about the sharp maps between `A` and its
reciprocal class enter the enumeration.
