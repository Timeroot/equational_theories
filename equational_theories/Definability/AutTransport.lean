import equational_theories.Definability.Aut_sym3
import equational_theories.Definability.Aut_alt45
import equational_theories.Definability.Aut_cyc5
import equational_theories.Definability.Aut_sym45
import equational_theories.Definability.Aut_rot3

/-!
# Refutations from symmetry

`Definability/Transport.lean` reduces "which operations on `Fin n` admit this group of symmetries"
to orbit data plus four `decide`s, so a symmetry group costs no mathematics -- only the size of the
family it has to search. That makes it worth sweeping groups wholesale rather than one at a time,
and the files imported here are the result, one per group.

For each group, the invariant operations are enumerated once and answer both questions a symmetry
obstruction asks. A source law is usable when some invariant operation models it: that operation is
then a model of the source whose automorphisms include the group. A target law is refuted when
*no* invariant operation models it. Every pair of the two is a cell, and the sweep is exhaustive
for that group -- if a symmetry obstruction on it can refute a cell at all, the cell is here.

Because the models are exhibited on `Fin n` and the symmetries are genuine permutations, each
theorem refutes `DefinableFrom`, the weakest of the four relations on the board and hence the
strongest one to refute; the finite-carrier flavours follow.

Cells are proved with the smallest family that refutes them, since that size is what
`native_decide` pays. The files are split by group because `native_decide` recompiles its whole
module on each invocation, which makes one large file quadratic.
-/
