# FO-structural separations from one exceptional row

Date: 2026-10-07. Arrows are source → target.

All nine unrestricted FO-structural arrows from a source class in
**{E1020, E1629, E3456}** to a target class in **{E8, E47, E3319}** are now
refuted in Lean. This separates nine previously unresolved pairs of
FO-structural equivalence classes, reducing the unrestricted inventory from
**1,000 to 991 unresolved class pairs**. Closure adds **48 directed negative
equation cells**, including duals and consequences. The finite FO versions of
these nine arrows remain open. The other nine relation boards are unchanged;
in particular these cells already had term-structural refutations.

Closure also refutes the three sources → E307 (and its dual E359).
Their reverse directions were already refuted, so these additional cells do
not contribute new equivalence-pair separations.

Six direct generators suffice:

| Source | Target | Lean declaration |
|---|---|---|
| E1832 (dual of E1629) | E3319 | `Equation3319_not_StructuralFrom_Equation1832_singleDefect` |
| E1832 | E47 | `Equation47_not_StructuralFrom_Equation1832_singleDefect` |
| E3862 (dual of E3456) | E3319 | `Equation3319_not_StructuralFrom_Equation3862_singleDefect` |
| E3862 | E47 | `Equation47_not_StructuralFrom_Equation3862_singleDefect` |
| E1020 | E3319 | `Equation3319_not_StructuralFrom_Equation1020_singleDefect` |
| E1020 | E47 | `Equation47_not_StructuralFrom_Equation1020_singleDefect` |

The three-point constructions share
[SingleDefectCounting.lean](../equational_theories/Definability/SingleDefectCounting.lean).
The four-point construction is in
[E1020SingleDefect.lean](../equational_theories/Definability/E1020SingleDefect.lean).
E8 implies E3319, so the E8 negatives follow from the displayed E3319 negatives.

## The three-point construction

An E8 row at `a` satisfies `f(a,f(a,a))=a`. On `n` points, the exact number
of such rows is

```
R(n) = n^(n−1) + (n−1)n^(n−2),
```

counting a fixed point or a two-cycle through `a`. Thus `N₈(n)=R(n)^n`.

Choose three distinct points `x,s,t`. Give every row except `x` the E8
property, and prescribe

```
x*x=s,   x*s=t,   t*t=t.
```

For E1832, additionally prescribe `t*s=x`. Its law at `x` becomes
`(x*(x*x))*(x*x)=t*s=x`. At every other point it follows from the E8 row
property. For E3862, instead prescribe `t*x=s`; its law at `x` becomes
`(x*(x*x))*x=t*x=s=x*x`, and again every other row works automatically.

The resulting table fails E8 at exactly `x`. It therefore recovers `x`,
then `s=x*x` and `t=x*s`. Distinct choices of the points and free entries
cannot produce the same table. Row `x` has two prescribed entries, row `t`
has two, and every other row has `R(n)` choices. The exact family size is

```
n(n−1)(n−2) · n^(2n−4) · R(n)^(n−2).
```

Lean proves, for either source and every `n≥4`,
`n N₈(n) ≤ 16 N_source(n)`. The constants are convenient bounds; no sharp
asymptotics are needed.

## The four-point construction

For E1020, choose distinct `x,s,t,u` and prescribe

```
x*x=s,   x*s=t,   x*u=x,   t*t=t,   t*x=u.
```

Every other row satisfies E8. The E1020 law at the exceptional point is
`x*((x*(x*x))*x)=x*(t*x)=x*u=x`. An E8 row satisfies E1020 directly.
Once again `x` is the unique E8 failure, and successive evaluations recover
`s,t,u`. The family has

```
n(n−1)(n−2)(n−3) · n^(2n−5) · R(n)^(n−2)
```

tables. Lean proves `n N₈(n) ≤ 32 N₁₀₂₀(n)` for `n≥6`.

## Why this rules out FO recovery

The existing exact counts and upper bounds give `N₄₇(n)≤N₈(n)` and
`N₃₃₁₉(n)≤4N₈(n)` for `n≥3`. Consequently each source-to-target table-count
ratio above is unbounded. The previously formalized compactness theorem says
that unrestricted FO-structural interpretation would instead give a constant
`K` with `N_source(n)≤K N_target(n)` for every positive `n`.

The formulas are allowed to depend on the source model. Compactness supplies
a **finite collection** of formula pairs covering all source models; that is
the reason the bound still follows. This step does not apply to a hypothesis
restricted to finite models, so the proof leaves the finite FO questions open.

## Validation

Both new modules and the full 17,210-job `Definability` build passed. The six
exported refutations have transitive `spectrum_assert ... complete` guards;
none uses `sorry`, a native decision procedure, or an external proof certificate.
The new modules each compiled in about eight seconds in this run. All table
counts and inequalities are symbolic.

The [pass report](../data/definability_single_defect_pass.json) records the six
generators, all 48 new cells, the nine separated class pairs, and the source
fingerprint. The audit rebuilds all ten boards from the Lean declarations and
checks them against the independently computed closure changes. The
[FO equivalence inventory](definability_structural_equivalence_gaps.md) and
[term-structural inventory](definability_term_structural_equivalence_gaps.md)
are regenerated from the same snapshot.
