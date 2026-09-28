# An eight-point obstruction to finite FO structural recovery

The cyclic NAND operation on three bits is

    f(x,y) = 7 xor (rot(x) and rot²(y)),

where rot cyclically permutes the bits. It satisfies E1483. The three
permutations

    p₀ = (2 4)(3 6),   p₁ = (2 4)(3 5),   p₂ = (2 4)(5 6)

each fail to preserve f, whereas rot preserves f.

The finite certificate says that **every E1485 operation on these eight
points that preserves rot must preserve at least one of p₀, p₁, p₂**. Thus
it cannot be first-order interdefinable with f: a definition of the E1485
operation from f preserves rot, and a definition back preserves its extra
permutation, contradicting one of the three checks on f.

This separates finite **FO structural recovery**. It does not disprove
finite FO definability of E1485 from E1483; that weaker relation asks for
only the forward definition.

The Lean implementation is split into:

* `Definability/Cyclic1483/Base.lean`: the source and its permutation checks;
* `Definability/Cyclic1483/FiniteEncoding.lean`: the finite constraint;
* `Definability/Cyclic1483/FiniteCertificate.lean`: the checked LRAT proof;
* `Definability/Cyclic1483/Bridge.lean`: transport from the encoding back to
  an arbitrary operation on `Fin 8`;
* `Definability/Cyclic1483Structural.lean`: the definability argument and
  final theorem `Definability.Cyclic1483.Equation1485_not_structuralFromFin_Equation1483`.

The finite constraint uses 192 table bits. Rotation invariance leaves only
64 effective bits: four fixed input pairs have one output bit each, and
twenty orbits of size three have three bits each. It checks 176
representatives of the law's three-variable instances and tests the three
extra permutations. Every constraint is derived from the actual operation
in the bridge; no symmetry-breaking assumption is imposed on the target.

The checked certificate is the approximately 15 MiB binary file
`Definability/Cyclic1483/FiniteCertificate.lrat`, SHA-256
`d9b0e7059222c8552a4eabeaf1ec7ad69e578a109d2e328d08b9010616412b24`.
Ordinary builds use `bv_check` to replay this file and do not rerun SAT.
The proof uses Lean's compiled, verified LRAT checker. Its guarded final
axiom audit contains exactly `propext`, `Classical.choice`, `Quot.sound`, and
`Definability.Cyclic1483.FiniteCertificate.certificate._native.bv_decide.ax_1_5`.
The last name is the compiled LRAT check, also when replayed with `bv_check`.
There are no additional native or admitted axioms. This differs from the
new general-linear FO negatives, which use only the three standard axioms.

`scripts/generate_cyclic1483_structural.py` regenerates the encoding and
transport files. `scripts/definability_cyclic1483_structural.py` separately
replays the exploratory Z3 search, with direct checks of every positive
table and permutation group. Its saved record is
`data/spectrum/1483_cyclic8_structural_search.json`. Z3's external UNSAT
answer motivates the constraint; the saved LRAT replay supplies the
Lean verification.
