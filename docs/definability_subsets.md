# Subalgebra obstruction: E3352 → E4408

18 September 2026. The eight-element model in
[SubsetObstruction.lean](../equational_theories/Definability/SubsetObstruction.lean)
refutes **E3352 → E4408 in TS/fin**, hence also TS/all.
Under existing equivalences this removes the four raw pairs
`{3352,4164} → {4408,4479}` from the completely-open table:
**36 → 32 raw pairs, 10 → 9 class rows**.
It does not settle the one-way term or first-order definability variants.

## Argument

Every binary term preserves every subalgebra and every compatible relation of
its source operation. Mutual term definitions therefore preserve the exact
idempotent set and the exact family of subalgebras.

The source has one idempotent, labelled `3`. Its operation fails to preserve
both `S = {0,1,2,4,5,6,7}` and `T = {0,3}`: the witnesses are `0 ◇ 1 = 3`
and `0 ◇ 0 = 7`, respectively.

Six compatible binary relations constrain every source term operation. They
are the graphs of the automorphism `(0 7 1)` and its inverse;
`G × {5,6} ∪ {3} × {2,4}`; and three partial maps with domain `{2,4,5,6}`
and respective value lists `[5,6,5,6]`, `[6,5,5,6]`, and `[4,2,5,6]`.

The finite coverage theorem proves that any operation satisfying E4408,
preserving those six relations, fixing `3`, and not fixing `0`, `5`, or `6`
on its diagonal preserves either `S` or `T`. The idempotent conditions follow
from mutual term definability. Preservation of either set then prevents
recovery of the source operation. This excludes every binary term, without a
term-size bound or a claim that the forward invariant describes the full clone.

## Certificate and checks

[The generated Lean certificate](../equational_theories/Definability/Generated/Subset3352.lean)
encodes each operation as eight 24-bit rows and proves the finite contradiction
with `bv_decide`. Its 68 necessary constraints are 30 instances of E4408,
four diagonal conditions, and 34 compatible-relation instances. The encoding
lemma connects every bit-vector lookup to the original arbitrary operation.
The source law and the six relations are checked separately by kernel `decide`.

`bv_decide` checks an LRAT certificate through Lean's standard compiled
evaluation mechanism. Consequently the final theorem has the generated native
certificate-checking axiom in addition to the usual classical Lean axioms;
this is recorded by an axiom guard. The external Z3 replay is an independent
check and is not used as a Lean axiom.

```sh
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_subset_check.py --check
lake build equational_theories.Definability.SubsetObstruction
```

The Python checker verifies the model, all six source-compatible relations,
the inputs of every selected relation instance, and the two failed source
subalgebras. It rebuilds the minimized SMT problem from
[the saved data](../data/definability_subset_3352.json) and requires `unsat`.
`--write` regenerates the Lean certificate deterministically.

The earlier four-family unary-recovery search remains available in
[the residual report](definability_residual_candidates.md). The two-subset
argument above supplies the completed whole-row obstruction.
