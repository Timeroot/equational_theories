# Reversible cube-column repair

Date: 2026-09-21.

[`CubeColumnRepair.lean`](../equational_theories/Definability/CubeColumnRepair.lean)
proves **E3471, E317, E3283, E3270, and E3280 → E108** FO-structurally over
arbitrary carriers, hence also over finite carriers. Each direction of each
interpretation is quantifier-free and parameter-free. The five exported
conclusions have standard-axiom guards.

| Source | Target | Lean declaration |
|---:|---:|---|
| 3471 | 108 | [`Equation108_StructuralFrom_Equation3471_cubeColumn`](../equational_theories/Definability/CubeColumnRepair.lean#L184) |
| 317 | 108 | [`Equation108_StructuralFrom_Equation317_cubeColumn`](../equational_theories/Definability/CubeColumnRepair.lean#L195) |
| 3283 | 108 | [`Equation108_StructuralFrom_Equation3283_cubeColumn`](../equational_theories/Definability/CubeColumnRepair.lean#L206) |
| 3270 | 108 | [`Equation108_StructuralFrom_Equation3270_cubeColumn`](../equational_theories/Definability/CubeColumnRepair.lean#L217) |
| 3280 | 108 | [`Equation108_StructuralFrom_Equation3280_cubeColumn`](../equational_theories/Definability/CubeColumnRepair.lean#L228) |

For a source operation M, write `s(y) = M(y,y)` and `c(y) = M(s(y),y)`.
The shared hypotheses say that each s(y) is a right zero and that `c(y)=y`
forces `s(y)=y`. Each of the five source equations implies these hypotheses.

The construction modifies columns. A column with `s(y)=y` becomes the identity
column. If `c(y)=s(y)` and `s(y)≠y`, it remains unchanged. Otherwise y, s(y),
and c(y) are distinct, and the inputs at those three positions are cyclically
reassigned. The new diagonal is the old c, and the new right cube is the old s.
Columns indexed by s(y) become identity columns, giving E108.

The new diagonal and right cube identify the same distinguished positions,
so the inverse definition undoes the cycle and restores each constant column.
The proof includes the coincident-position cases and uses no finiteness
assumption. The table above links each exported declaration.

These are FO-structural positive results. They do not assert term-structural
interpretations. The regenerated [FO inventory](definability_structural_equivalence_gaps.md)
records which equivalence directions they settle after closure.
