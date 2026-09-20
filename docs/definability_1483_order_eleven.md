# E1483 has no eleven-element model

20 September 2026. Lean now proves `Spectrum.not_order_1483_11` and the resulting
finite first-order definability negative **E1486 → E1483**. This removes the
four raw pairs `{1486,2126} → {1483,2163}` from the completely open inventory.
All eight definability variants are negative on that rectangle.

The existing eleven-element E1486 model supplies the source carrier. The new
argument excludes **every** E1483 operation on that carrier, so no definability
or recovery restriction on a hypothetical target operation is needed.

## Mathematical reduction

Write `f` for the hypothetical operation and `r(a)` for the cardinality of its
row image. E1483 is

```
f(f(y,x), f(x,f(y,z))) = x.
```

The [translation identities](../equational_theories/Definability/Central1483Translations.lean)
and [constant-row argument](../equational_theories/Definability/Central1483Constant.lean)
show that no row is constant or bijective at order eleven. Left and right
translation at any element have equally sized images. Every image edge gives
`11 ≤ r(a) · r(b)`, and an idempotent satisfies `11 ≤ r(a)²`.

The [normalization proof](../equational_theories/Definability/Central1483Normalization.lean)
chooses a minimum-rank row and relabels it as row zero. Its image becomes
`{0,…,k−1}` or `{1,…,k}`, its diagonal output is zero or one, and its entries at
input labels larger than `k` are sorted. The minimum rank is between two and
ten. If the image contains zero, the edge bound requires `11 ≤ k²`, eliminating
that alternative for ranks two and three. There are therefore exactly sixteen
cases: one each at ranks two and three, and two each at ranks four through ten.

[Central1483SAT.lean](../equational_theories/Definability/Central1483SAT.lean)
proves that any normalized model satisfies its corresponding propositional
formula. Clauses encode the operation table, exact row and column images,
E1483 and its proved dual, translation regularity, rank bounds, and the proved
label normalization. Tautological clauses are removed with a proved transfer
lemma. The model-to-CNF proof and normalization use only the three standard
Lean axioms.

## Refutation certificates and trust

CaDiCaL generated an LRAT refutation for each case. Unused additions and deletion
steps were removed, with surviving identifiers renumbered. The sixteen retained
proofs contain **4,646,678 additions**. Their compressed inputs occupy
**769,167,024 bytes**; the expanded textual proofs occupy 2,855,536,848 bytes.

Each [generated module](../equational_theories/Definability/Generated/Central1483Rank4Zero1.lean)
checks its actual proof against the Lean-defined formula with Lean's LRAT checker
and applies the checker's soundness theorem. Gzip decompression occurs during
elaboration and produces a string literal. The theorem depends on that literal
and its checked contents; it does not assume that the external decompressor or
solver is correct. Generated source comments contain content hashes so a changed
certificate changes its generated module and invalidates its build cache.

The final theorem's axiom guard records `propext`, `Classical.choice`,
`Quot.sound`, and **sixteen explicit native computation axioms**, one for each
LRAT check. This is a computational certificate, unlike the ordinary-axiom
proofs of the previously completed E167/E168/E1485 spectrum obstructions.

The [manifest](../data/definability_1483_order_eleven.json) records every case,
compressed and expanded hashes, proof and clause counts, and the generated
module's axiom record. The independent checker reconstructs all sixteen CNFs,
checks the complete partition, verifies hashes and LRAT identifier structure,
and reproduces every generated module. Logical validity of LRAT steps is checked
by Lean, not by that Python metadata checker.

## Completed consequence and reproduction

[Central1483OrderEleven.lean](../equational_theories/Definability/Central1483OrderEleven.lean)
combines the cases into the exclusion theorem.
[CentralSpectrum.lean](../equational_theories/Definability/CentralSpectrum.lean)
then proves `Equation1483_not_definableFromFin_Equation1486_spectrum` from the
existing E1486 witness. All sixteen individual checks, the combined exclusion,
and the finite-FO consequence have compiled with explicit axiom guards.

```sh
python3 scripts/definability_1483_sat_check.py
lake build equational_theories.Definability.CentralSpectrum
```

The checker can export independently reconstructed DIMACS inputs with
`--export-cnf DIRECTORY`. This result concerns order eleven; it does not prove a
general prime-order exclusion or determine the exact E1483 spectrum.
