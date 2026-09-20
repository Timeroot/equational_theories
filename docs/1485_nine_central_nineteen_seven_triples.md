# Nine central elements: one nineteen-top type is impossible

Research theorem, 20 September 2026. This is an analytic reduction
followed by one independently checked LRAT refutation. The mathematical
normalization and encoder were independently audited. It is not a Lean
theorem and does not exclude every nineteen-top configuration.

Assume a finite E1485 magma has minimum translation degree four,
nine central elements, and first noncentral top-product degree five.
Let `N_pc` count tops with central block sizes `(|P|,|C|)=(p,c)`.

**Theorem.** The following nineteen-top type table is impossible:

\[
N=\begin{pmatrix}9&0&0\\0&0&3\\0&3&4\end{pmatrix}.
\]

No total-order-forty bound is needed. The theorem applies in particular
to the order-forty investigation, where the first-output degree is five.

## 1. Complete normalization of the central incidence

Each central row has four tops whose `C` blocks partition nine labels.
Its size pattern is `3321` or `3222`. The nine `(1,1)` tops have
distinct singleton `P` blocks: a repeated label would put two singleton
`C` blocks in the same row. Thus these nine blocks partition `Z`.
Every central row is consequently `3321` and contains exactly one
size-two `C` block. Those blocks belong precisely to the three `(3,2)`
tops, so their `P`-triples partition `Z`. Dually the `C`-triples of
the three `(2,3)` tops partition `Z`.

Every cross-intersection of these two triple partitions is at most one.
They therefore give a full three-by-three grid. Choose their top names
and the central labels so that the `(3,2)` predecessor blocks are its
rows and the `(2,3)` successor blocks its columns. Afterwards name each
singleton/singleton top by its unique predecessor label. This fixes
its `P` block but does **not** fix its `C` singleton; their permutation
is left entirely unrestricted. No other block is assumed grid-aligned.

## 2. A four-top first-output profile must exist

A degree-five first top output has profile size three or four, by the
[first-output profile theorem](1485_first_successor_degree_profiles.md)
and the central-cardinality bound. Size three is impossible here:
the [complement-tiling theorem](1485_nine_central_three_profile.md)
would give at most six global `P`-triples, whereas the displayed
table has seven. Thus there exist sets `U,V` of four tops each such
that `P_U` and `C_V` partition `Z`, and the central-intersection
matrix `K[U,V]` is a permutation matrix.

## 3. The finite contradiction

The [deterministic encoder](../scripts/1485_nine_central_h19_seven_triples_cnf.py)
uses the actual nineteen-by-nine incidence bits for `P,C`. It requires
the displayed block sizes, central valency four, a partition of the
central square by `P_t×C_t`, and `|C_s∩P_t|≤1`. It implements the
complete normalization in §1 and existentially chooses `U,V` from §2.

For the selected `K` submatrix, four selected intersection events are
required in total, with at most one per row and column. Together with
four chosen rows and columns, this is exactly a permutation matrix.
The subsets themselves are not otherwise normalized or restricted.

The resulting formula has 29,005 variables and 89,611 clauses. A text
LRAT refutation was produced in 42.88 seconds and accepted by an
independent checker in 0.89 seconds. Regeneration from the packaged
source gave the identical CNF hash. The
[certificate inventory](../data/1485_certificates/NINE_CENTRAL_H19.md)
records the retained proof, source hashes, controls, and replay commands.

Bare central incidence is **not** contradictory for this table: a
separate SAT fixture was directly checked against all central incidence
conditions. The first-output profile constraint is a substantive part
of this proof. The other two nineteen-top count tables remain outside
the scope of this theorem when the first output has profile size four.
