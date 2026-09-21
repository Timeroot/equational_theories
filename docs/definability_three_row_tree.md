# E1133/E1167: recovery, ray companions, and a three-row counterexample

Date: 2026-09-21.

The unrestricted E1133/E1167 equivalence question remains open. This pass
settles two concrete questions about proposed approaches, with Lean proofs:

* The successor-ray E1167 model has a first-order interdefinable E1133 companion.
  It cannot witness an FO-structural negative E1167 → E1133.
* The term `x □ y = (x*x)*y` always permits term recovery when the source
  satisfies E1133, but it does **not** always produce an E1167 operation.
  An explicit infinite tree with three different row operations refutes it.

No equivalence classes were merged or separated in this pass: 34 unrestricted
term-structural class pairs remain unresolved, and the finite classification
still has exactly 716 classes.

## Two rays with first-order recovery

On the natural numbers, using truncated subtraction, define

```text
M(x,y) = y+1 if x,y have equal parity; y-1 otherwise.
N(x,y) = y-1 if x,y have equal parity; y+1 otherwise.
```

`M` satisfies E1167, `N` satisfies E1133, and `N(x,y) = M(M(x,x),y)`.
Their square maps are successor and truncated predecessor, respectively.
The reverse first-order definition is

```text
M(x,y) = z  iff  ∃u, N(u,u)=x ∧ u≠x ∧ N(u,y)=z.
```

The first two conditions select `u=x+1`; the last then reads the original row.
This is a parameter-free formula. In contrast, **this particular** companion
cannot term-define `M`: every term in `N` sends `(0,0)` to `0`, while `M(0,0)=1`.
Other possible E1133 companions of `M` are not excluded by that argument.

[UnaryRayCompanions.lean](../equational_theories/Definability/UnaryRayCompanions.lean)
checks both laws, the formula and its semantics, and the term-recovery obstruction.
The predecessor ray also gives a shorter proof of the already established
E1133 → E1096 unrestricted term-structural negative.

## Recovery is valid, but the target law fails

For any E1133 operation, let `S(x)=x*x` and `T(x)=(x*x)*x`. The law gives

```text
x*(x*y) = y,
((z*y)*y)*x = (z*y)*x,
S(T(x)) = x.
```

Consequently, if `F(M)(x,y)=M(M(x,x),y)`, then `F(F(M))=M`, and the square
map of `F(M)` is injective. These facts alone do not establish E1167 for `F(M)`.

The counterexample in
[ThreeRowTree.lean](../equational_theories/Definability/ThreeRowTree.lean)
uses three rooted trees. A vertex is a root index in `{0,1,2}` and a reduced
word in three involutions `P₀,P₁,P₂`. Applying `Pⱼ` adds or cancels the first
letter `j`. Eleven finite states assign each vertex a color `c(v)` and an
idempotent map `fᵥ : {0,1,2} → {0,1,2}` satisfying

```text
c(Pⱼ(v)) = fᵥ(j).
```

The magma operation is `u*v = P_c(u)(v)`. To check E1133, set `w=P_c(z)(y)`.
Involutivity gives `f_w(c(z))=c(y)`, and idempotence gives `f_w(c(y))=c(y)`.
Thus `c(y*(z*y))=c(y)`, so the two outer rows cancel as required.

The three states along a selected path from root 1 are

| Vertex | Color | Profile `(f(0),f(1),f(2))` |
|---|---:|---|
| `y` | 1 | `(1,1,1)` |
| `P₁(y)` | 1 | `(0,1,0)` |
| `P₂(P₁(y))` | 0 | `(0,1,1)` |

For the transformed operation, taking `x`, `y`, and `z` to be roots 0, 1,
and 2 makes the right-hand side of E1167 equal to `P₁(P₀(x))`, which differs
from `x`. Lean checks the finite transition conditions, the law on every
vertex of the infinite trees, and this explicit violation. The source is
infinite; no finite-model search could have found this counterexample.

## Wider recovery probe

A sweep revisited 81 stored candidates for the remaining unrestricted
term-structural equivalence arrows. With a three-second Vampire budget per
obligation, 51 recovery identities were proved, but no target-law obligation
was proved. These are bounded proof-search outcomes, not 81 refutations.
The longer E1133 square-row searches were subsequently resolved by the
explicit counterexample above.

The [saved candidates and outcomes](../data/definability_equivalence_recovery_probe.json)
retain the defining and recovery terms for future searches. All final Lean
theorems have axiom guards permitting only `propext`, `Classical.choice`,
and `Quot.sound`.

Regenerate the 162 proof obligations with
`python3 scripts/definability_equivalence_recovery_probe.py /tmp/recovery-probe`.
Pass `--vampire /path/to/vampire --seconds 3` to retry them.

Validation: the full 16,986-job `Definability` build passed; the audit's ten
closure calculations matched the full-matrix reference; `--check` passed;
and both equivalence inventories were regenerated against the new snapshot.
All 162 regenerated TPTP obligations matched those used in the saved probe.
