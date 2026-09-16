# Reversible companions and proof cleanup

First pass of 16 September 2026; the subsequent
[argument-swap pass](definability_argument_swap.md) extends this work.
These are Lean proofs over **arbitrary** carriers, not
bounded finite searches. The [open-cell audit](definability_open_audit.md)
tracks the remaining questions; this document explains the new mathematics
and where the proofs live.

## Organization

| Module | Responsibility |
|---|---|
| [Reversible.lean](../equational_theories/Definability/Reversible.lean) | Turn an explicit quantifier-free inverse into structural definability; define and invert the square-swap companions; discharge automorphism obligations for trivial case trees. |
| [SquareSwap.lean](../equational_theories/Definability/SquareSwap.lean) | Source-law lemmas, target-law proofs, six arbitrary-carrier structural theorems, and the old finite corollaries. |
| [LFO3_00.lean](../equational_theories/Definability/LFO3_00.lean) through [LFO3_09.lean](../equational_theories/Definability/LFO3_09.lean) | Preserve 55 existing guard-certificate statements with short normal-form proofs and axiom checks. |
| `Ja_3519`, `Ja_3522`, `Mne_3503`, `Mne_3869`, `Mne_4633` | Compatibility imports: the old entry points and finite theorem names still work. Their proofs now live together in `SquareSwap`. |

No imports were removed from `Definability.lean` in this first pass. All 13,325
previously reachable local modules remain reachable; the two new modules bring
the total to 13,327. All 61 old theorem names and statements are retained:
55 guard obligations and six finite structural conclusions. Their statements
were compared with their previous versions, not merely their names.

The affected proof modules occupied **77,321 lines**. Including both new shared
modules and their axiom checks, their replacement occupies **1,199 lines**:
**76,122 fewer lines**. This is proof compression, not deleting unresolved
obligations or omitting certificates from the build.

## The reversible operation

Write `d(x) = x*x`, and let `swap(a,b)` exchange two elements and fix the rest.
When `a=b`, this is the identity. Define

```text
S(*)(x,y) = swap(d(x), d(y))(x*y).
T(*)(x,y) = swap(d(x), d(y))(y*x).
```

These are quantifier-free definitions: test whether the output equals either
square, and replace it with the other square if so. Both preserve the entire
square map: `S(*)(x,x) = T(*)(x,x) = d(x)`. Therefore the same swaps are used on
a second application, and each swap is its own inverse:

```text
S(S(*)) = *,       T(T(*)) = *.
```

For the opposite version, swapping the arguments exchanges the two square
values, which does not change their transposition. These identities need **no
source law, finiteness, cancellation, or distinctness of squares**.

Consequently, to prove a structural arrow using either companion, only its
target law remains to be proved. `structuralFrom_of_qfInverse` expresses the
general pattern, allowing different forward/inverse definitions and recovery
that uses the source law. The two specialized square-swap helpers supply their
universal inverses automatically.

This is a genuine arbitrary-carrier recovery argument. Equality of automorphism
groups, which supplied the previous finite results, would not suffice here.

## Six formerly open structural/all cells

Arrows below are **source → target**; Lean writes `LawTarget.StructuralFrom
LawSource`. All six finite versions were already known. These are six directed
cells, not six independent mathematical ideas: the two E3503 conclusions share
one proof, and all six use the same reversible construction.

| Source | Target | Companion | Target proof |
|---|---|---|---|
| E3503 | E3470 | `S` | Squares are right-zero elements; nested products give the required columns. |
| E3503 | E3460 | `S` | Specialize the E3470 target law. |
| E3869 | E3462 | `T` | Squares are left-zero elements, with a second constant-row identity. |
| E4633 | E3253 | `T` | The row of `(x*x)*x` is constant. |
| E3519 | E3253 | `T` | Split the square-swap cases and use the source law. |
| E3522 | E3253 | `T` | Split the square-swap cases and use the source law. |

The corresponding theorem names are
`EquationTARGET_StructuralFrom_EquationSOURCE` in `SquareSwap.lean`.
The `StructuralFromFin` names are corollaries of these stronger statements.
For all six pairs, term-structural definability was already refuted even on
finite carriers, while term-definability without recovery was already proved.
The missing property was FO recovery over arbitrary carriers; the case-defined
swaps supply it without claiming term recovery.

After closure with the existing results, these settle **24 structural/all
class cells, representing 100 raw equation pairs**. The 739 structural/all
classes are unchanged, so this decrease is not an artifact of merging classes.
The complete list of newly resolved class pairs is:

| Source class representative(s) | Target class representative(s) |
|---|---|
| 3477 | 3462 |
| 3503 | 3457, 3459, 3460, 3462, 3463, 3465, 3466, 3468, 3469, 3470 |
| 3519, 3520, 3522, 3523, 3525, 3526, 3529, 3532, 3533, 3534, 3537, 3541, 4296 | 3253 |

Each row denotes every source–target combination in that row. E3869 belongs
to class 3477 and E4633 to class 4296. These are closure consequences, not
24 independent constructions. The structural/all open count falls from
61,974 to 61,950 class cells (451,072 to 450,972 raw pairs). The other nine
boards and all negative counts are unchanged. The exhaustive snapshot was
regenerated with full-matrix verification in 147.12 seconds.

### E3503: right-zero squares

The source law is `x*x = y*((z*w)*x)`. For fixed `a`, let `c=(a*a)*a`.
The law gives `z*c=d(a)` for every `z`. Substituting at `c` shows that
`b*d(a)=d(a)` for every `b`: squares are right-zero elements.

For the companion, this yields `S(*)(a,d(b))=d(a)`. Directly from the source
law, also `S(*)(a,(b*c)*d)=d(a)`. Every companion output is either a square
or an original product. Splitting these three possibilities for the inner
outputs therefore gives

```text
d(x) = x □ ((y □ z) □ w),
```

which is E3470 for `□=S(*)`. Taking `y=x` gives E3460.

### E3869: left-zero squares

Here `d(a)=(a*(b*a))*c`. The row of `a*(a*a)` is constantly `d(a)`;
substitution gives the two useful consequences

```text
d(a)*b = d(a),       (a*d(b))*c = d(a).
```

Splitting the opposite companion's cases, these imply E3462:
`x□x = x□((y□x)□y)`. The named lemmas expose the algebra; `grind` closes
the remaining finite equality cases inside Lean.

### E4633: a constant cube row

The law is `(a*b)*a=(a*c)*c`. Apply it with first argument `a*b`, comparing
the second arguments `a*b`, `a`, and `b`. Substituting the original law
shows that the row of `c(a)=(a*a)*a` is constant. In particular,
`c(a)*b=c(a)*c(a)`. This identity closes the cases needed for E3253:
`x□x = x□(x□(x□x))`, again for `□=T(*)`.

## Why the large guard proofs disappeared

Each of the 55 deep two-guard decision trees was pointwise just `x*y` or
`y*x`. A branch that appeared to return a different term had a guard implying
that the terms were equal. Thus two case splits and equality simplification
establish the normal form. The automorphism obligation follows once, in
`guardAut2_of_eq_op` or `guardAut2_of_eq_opposite`.

The original replay files proved these same obligations in tens of thousands
of steps. Their replacement does not use a stronger source hypothesis; the
normal-form lemmas work for any law. This cleanup alone settles no new board
cells: the six stronger structural statements above are the new results.

## Trust and extending the pattern

Every new structural conclusion has a `#guard_msgs` / `#print axioms` check.
Each normal-form file checks all its theorems' transitive axiom dependencies
under `#guard_msgs`. Only `propext`, `Classical.choice`, and `Quot.sound` are
permitted: no `sorryAx`, native decision axioms, or external ATP trust.
These checks cover the changed proofs, not the entire historical repository.

With dependencies cached, the ten normal-form modules, including all 55 axiom
checks, built together in **4.53 seconds** elapsed. `SquareSwap` took **9.5
seconds** in Lean, **10.91 seconds** including Lake overhead. The final
incremental `Definability` entry-point build succeeded in **73.28 seconds**
(16,628 jobs considered). These are local wall-clock observations, not a cold
build comparison with the deleted replays.

For another candidate, first simplify its case-defined operation, then seek an
explicit inverse. If it is one of these swaps, import `Reversible`, prove the
target law, and apply the appropriate helper. Keep the source-law algebra
separate from recovery. A finite automorphism proof by itself is not grounds
for changing `StructuralFromFin` to `StructuralFrom`.
