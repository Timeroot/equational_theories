# The remaining eighteen-top profiles at nine central vertices

Research note, 20 September 2026. **Completed external finite proof:**
three profile cases below have analytic exclusions; the other five have
retained, independently checked LRAT refutations. The mathematical
reduction, normalization, and CNF encoder were independently audited.
This is not a Lean proof and does not settle the spectrum conjecture.

**Theorem.** Minimum degree four, nine central elements, and a
degree-five first top output with three top predecessors and successors
force the number of top elements to be sixteen or seventeen. The
[previous analytic argument](1485_nine_central_three_profile.md)
left only sixteen, seventeen, or eighteen; the present note excludes
eighteen. No total-order-forty assumption is used.

Assume minimum degree four, nine central elements, and a degree-five
first top output with three top predecessors and successors. The
[nine-central profile argument](1485_nine_central_three_profile.md)
reduces eighteen tops to the central type tables

\[
 A=\begin{pmatrix}6&0&0\\0&3&3\\0&3&3\end{pmatrix},
 \qquad B=\begin{pmatrix}5&1&0\\1&3&2\\0&2&4\end{pmatrix}.
\]

Both have six `P`-triples and six `C`-triples. Each triple family
covers every central label twice, and every `C`-triple intersects
every `P`-triple exactly once. Fix the size-three profile `(U,V)`.
Write `u` for the number of `C`-triples indexed by `U`, `v` for
the number of `P`-triples indexed by `V`, and `o=|U∩V|`.

## Complete profile normalization

The `u` by `v` all-one submatrix of the permutation `K[U,V]`
forces `u=v=1` if both are nonzero. Otherwise at least one is zero.
Duality exchanges `u,v`; both type tables are self-dual. Thus:

| Type | `(u,v,o)` | Status here |
| --- | --- | --- |
| A | `(0,0,0)` | Analytic triangle exclusion below |
| A | `(0,1,0)` | Checked LRAT refutation A010 |
| A | `(0,2,0)` | Analytic missing-column exclusion below |
| A | `(0,3,0)` | Analytic partition exclusion below |
| A | `(1,1,0)` | Checked LRAT refutation A110 |
| A | `(1,1,1)` | Checked LRAT refutation A111 |
| B | `(1,1,0)` | Checked LRAT refutation B110 |
| B | `(1,1,1)` | Checked LRAT refutation B111 |

For B, only two tops have type `(3,2)` and only two have type
`(2,3)`, forcing `u,v≥1`. If `u=0` or `v=0`, the profile
sets are disjoint. When `u=v=1`, their sole possible common top
is the unique `(3,3)` top chosen on each side; it may coincide or
not. Permutations of the labels within each central type identify
all choices with the same listed triple. This accounts for every
profile, not merely a subclass with specially aligned blocks.

The sets `P_U` and `C_V` partition the nine labels into triples;
every cross-intersection is one. Their grid gives coordinates
`(i,j)` with `P_(U_i)` the three rows and `C_(V_j)` the three
columns. **No other global block is required to lie in a row or
column.** In fact the other triples can be arbitrary transversals
to the opposite partition, subject to central incidence.

## Three analytic exclusions

For every A case with `u=0`, the set `U` is exactly the three
`(3,2)` tops. Its complementary three `P`-triples, denoted `S`,
are the `(3,3)` tops and also form a partition of the central set.

If `v=3`, then `V=S`; a row of `K[U,V]` has sum `|C_u|=2`,
not one. This excludes `(0,3,0)`.

If `v=2`, write `V=(S∖{w})∪{b}`, where `b` has type `(2,3)`.
For each `u∈U` the row sum is

\[
 1=2-K_{uw}+K_{ub}.
\]

Zero-one entries force `K_uw=1` and `K_ub=0`. The column indexed
by `b` is consequently zero, contradicting a permutation matrix.
This excludes `(0,2,0)`.

Suppose finally `v=0`. Each central row contains one top from `U`
and one from `S`, contributing `C`-sizes two and three. Its two
other blocks therefore have sizes `1+3` or `2+2`. The double
blocks in the latter alternative must come from the three tops of
type `(2,2)`; the `(3,2)` tops are already in `U`.
It follows that the three `P`-pairs of the `(2,2)` tops form a
loopless multigraph in which every nonzero vertex degree is two.
A loopless two-regular multigraph with three edges is a triangle:
a parallel pair would leave one edge with degree-one endpoints.
The dual argument, using that `V` is all three `(2,3)` tops,
makes their three `C`-pairs a triangle too. Two distinct `(2,2)`
tops then have intersecting `P`-blocks and intersecting `C`-blocks;
their central rectangles overlap. This excludes `(0,0,0)`.

## Necessary finite constraints for the other five cases

The [deterministic encoder](../scripts/1485_nine_central_h18_cnf.py)
encodes the actual `P,C` incidence bits on nine
central labels and eighteen tops:

1. All block sizes equal the selected type table, and every central
   label belongs to four blocks in each direction.
2. The eighteen rectangles `P_t×C_t` partition the central square;
   every cross-intersection `C_s∩P_t` has size at most one.
3. The six triples cover each label twice in each direction.
4. The normalized `P_U,C_V` are grid rows and columns, and
   `K[U,V]` is a permutation matrix, not necessarily the diagonal.
5. The small `P`-blocks split into the three disjoint auxiliary
   tilings of column complements, and dually the small `C`-blocks
   split into tilings of row complements.

These conditions follow from the preceding profile theorem in any
finite order. For an order-forty-only check one may additionally
require each complement tiling to use at most five blocks: the
translation fiber has size `40/5=8`, of which three inputs are
central. This extra bound must not be silently used for an
order-independent assertion. The archived proofs do **not** use that
extra bound.

The [certificate inventory](../data/1485_certificates/NINE_CENTRAL_H18.md)
retains all five compressed proofs, exact hashes, checker provenance,
and solver-free replay instructions. Every formula has at most 16,996
variables and 52,384 clauses. Generation took 0.554–1.021 seconds per
case; refutation took 3.84–30.26 seconds. An independent second-agent
replay regenerated all five CNFs, checked all fifteen CNF/raw/archive
hashes, and verified the five LRAT proofs in 3.46 seconds total.
Positive central-incidence fixtures and one-bit corruptions test the
common encoding; those fixtures are not claimed to satisfy the full
inconsistent formulas.
