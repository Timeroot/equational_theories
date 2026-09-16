# Argument-swap structural constructions

16 September 2026, following the [square-swap pass](definability_reversible.md).
These results concern **arbitrary carriers**, not testing through a finite size.

## The construction

Let `swap(x,y)` exchange `x` and `y`, fixing every other element; if `x=y`,
it is the identity. For any binary operation `*`, put

```text
A(*)(x,y) = swap(x,y)(x*y),
B(*)(x,y) = swap(x,y)(y*x).
```

Each is a quantifier-free, parameter-free definition using two equality tests.
The square map is unchanged, and both transformations are involutions:

```text
A(A(*)) = *,       B(B(*)) = *.
```

For `A`, apply the same transposition twice. For `B`, reversing the inputs
exchanges the transposition's endpoints, but `swap(y,x)=swap(x,y)`; again the
two swaps cancel. These facts need no source law or finiteness assumption.
The order of the two tests is irrelevant, giving four syntactic variants.

[ArgumentSwap.lean](../equational_theories/Definability/ArgumentSwap.lean)
defines all four as `QFOp.argumentSwap opposite reverse`, proves their action
and inverses, and supplies `structuralFrom_argumentSwap`. A source-specific
proof that the companion satisfies the target law is the only remaining
obligation.

## Two elementary cases

Write `d(x)=x*x` and `□=B(*)`. Its square is also `d(x)`.

**E31 → E312.** E31 says `d(x)*y=y`: every square is a left identity.
Consequently

```text
y □ d(x) = swap(y,d(x))(d(x)*y) = swap(y,d(x))(y) = d(x).
```

Thus squares become right-zero elements, exactly E312. This is the lemma
`ArgumentSwap.equation312`.

**E359 → E8.** E359 says `d(x)*x=d(x)`. Therefore

```text
x □ d(x) = swap(x,d(x))(d(x)*x) = swap(x,d(x))(d(x)) = x.
```

This is E8, proved by `ArgumentSwap.equation8`. Neither calculation assumes
that `x` and its square are distinct.

## Reusing the existing proofs safely

The old `AutBox.structuralFromFin_iteOf2` has two separate inputs:

1. An automorphism/recovery argument using finiteness.
2. A proof that its explicit companion satisfies the target law, already
   quantified over **arbitrary** carriers.

The tactic `recover_argument_swap` reuses input 2 from the elaborated theorem
body and replaces input 1 by the universal inverse above. It does **not** treat
the finite theorem's conclusion as an arbitrary-carrier theorem.

The tactic requires the expected certificate application, extracts its actual
companion and target-law proof, rejects free variables (including captured
finite-carrier hypotheses), and checks definitional equality with one of the
four supported companions. It checks the resulting theorem against the goal.
Lean's kernel then checks the new proof term. If the old proof's representation
changes incompatibly, extraction fails rather than supplying a result anyway.

This avoids copying or re-elaborating long ATP replays. It introduces no axiom,
oracle, or native decision procedure. All 47 new conclusions have transitive
axiom checks allowing only `propext`, `Classical.choice`, and `Quot.sound`.
There are also regression checks that an unrelated goal and an unsupported
certificate shape are rejected.

## The generating set

[ArgumentSwapCatalogue.lean](../equational_theories/Definability/ArgumentSwapCatalogue.lean)
contains 47 explicit structural/all declarations: the two elementary arguments
above and 45 recovered target-law certificates. Arrows are **source → target**;
Lean writes the target first. Names follow
`EquationTARGET_structuralFrom_EquationSOURCE_argumentSwap`.

The search found 1,547 previously open directed pairs with existing finite
certificates of the four supported shapes, corresponding to 491 pairs in the
pre-update structural quotient. Greedy closure selection reduced this to the
47 generators below. This is a generating set, not a proof that 47 is minimal
or that these are independent mathematical questions. It covers the full
scanned family, not every kind of finite structural certificate.

| Source | Target(s) | Companion | Original target-law certificate module |
|---|---|---|---|
| 23 | 307 | `B` | [Lc_23](../equational_theories/Definability/Lc_23.lean) |
| 31 | 312 | `B` | [Lc_31_pyx_y_pyx_x_x_y_pyx](../equational_theories/Definability/Lc_31_pyx_y_pyx_x_x_y_pyx.lean) |
| 53 | 1223 | `B` | [Lc_53](../equational_theories/Definability/Lc_53.lean) |
| 104 | 1020 | `B` | [Jb_104](../equational_theories/Definability/Jb_104.lean) |
| 224 | 823 | `A` | [Lc_224](../equational_theories/Definability/Lc_224.lean) |
| 332 | 1223 | `B` | [Lc_332](../equational_theories/Definability/Lc_332.lean) |
| 335 | 614, 1426 | `B` | [Lc_335](../equational_theories/Definability/Lc_335.lean) |
| 359 | 8 | `B` | [Lc_359_pyx_y_pyx_x_x_y_pyx](../equational_theories/Definability/Lc_359_pyx_y_pyx_x_x_y_pyx.lean) |
| 365 | 817 | `B` | [Lc_365_pyx_y_pyx_x_x_y_pyx](../equational_theories/Definability/Lc_365_pyx_y_pyx_x_x_y_pyx.lean) |
| 377 | 817 | `B` | [Lc_377_pyx_y_pyx_x_x_y_pyx](../equational_theories/Definability/Lc_377_pyx_y_pyx_x_x_y_pyx.lean) |
| 384 | 817, 1223 | `B` | [Lc_384](../equational_theories/Definability/Lc_384.lean) |
| 433 | 3461 | `A` | [Jlf3_433](../equational_theories/Definability/Jlf3_433.lean) |
| 633 | 1020 | `B` | [Lc_633](../equational_theories/Definability/Lc_633.lean) |
| 854 | 1023 | `B` | [Wkg_854](../equational_theories/Definability/Wkg_854.lean) |
| 1101 | 316 | `B` | [Le_1101_pyx_y_pyx_x_x_y_pyx](../equational_theories/Definability/Le_1101_pyx_y_pyx_x_x_y_pyx.lean) |
| 2105 | 3473, 4484 | `B` | [Le_2105](../equational_theories/Definability/Le_2105.lean) |
| 2739 | 1023 | `A` | [Le_2739](../equational_theories/Definability/Le_2739.lean) |
| 3145 | 439, 3318 | `A` | [Mwf_3145](../equational_theories/Definability/Mwf_3145.lean) |
| 3147 | 316 | `B` | [Le_3147_pyx_y_pyx_x_x_y_pyx](../equational_theories/Definability/Le_3147_pyx_y_pyx_x_x_y_pyx.lean) |
| 3272 | 817 | `A` | [Lc_3272](../equational_theories/Definability/Lc_3272.lean) |
| 3484 | 817 | `A` | [Lc_3484_pxy_y_pxy_x_x_y_pxy](../equational_theories/Definability/Lc_3484_pxy_y_pxy_x_x_y_pxy.lean) |
| 3566 | 3712 | `B` | [Le_3566](../equational_theories/Definability/Le_3566.lean) |
| 3587 | 647 | `A` | [Jr_3587](../equational_theories/Definability/Jr_3587.lean) |
| 3634 | 1691 | `B` | [Jc_3634_pyx_y_pyx_x_x_y_pyx](../equational_theories/Definability/Jc_3634_pyx_y_pyx_x_x_y_pyx.lean) |
| 3715 | 614, 1426 | `B` | [Lc_3715](../equational_theories/Definability/Lc_3715.lean) |
| 3735 | 1691 | `A` | [Jb_3735_pxy_x_pxy_y_y_x_pxy](../equational_theories/Definability/Jb_3735_pxy_x_pxy_y_y_x_pxy.lean) |
| 3735 | 820, 1023 | `B` | [Lc_3735](../equational_theories/Definability/Lc_3735.lean) |
| 3863 | 643 | `B` | [Le_3863_pyx_y_pyx_x_x_y_pyx](../equational_theories/Definability/Le_3863_pyx_y_pyx_x_x_y_pyx.lean) |
| 3907 | 658 | `B` | [Mwf_3907](../equational_theories/Definability/Mwf_3907.lean) |
| 3919 | 622, 1515 | `A` | [Le_3919_pxy_y_pxy_x_x_y_pxy](../equational_theories/Definability/Le_3919_pxy_y_pxy_x_x_y_pxy.lean) |
| 3919 | 1429 | `B` | [Le_3919_pyx_y_pyx_x_x_y_pyx](../equational_theories/Definability/Le_3919_pyx_y_pyx_x_x_y_pyx.lean) |
| 3926 | 622, 1515 | `A` | [Le_3926_pxy_y_pxy_x_x_y_pxy](../equational_theories/Definability/Le_3926_pxy_y_pxy_x_x_y_pxy.lean) |
| 3926 | 1429 | `B` | [Le_3926_pyx_y_pyx_x_x_y_pyx](../equational_theories/Definability/Le_3926_pyx_y_pyx_x_x_y_pyx.lean) |
| 3929 | 622, 1515 | `A` | [Le_3929_pxy_y_pxy_x_x_y_pxy](../equational_theories/Definability/Le_3929_pxy_y_pxy_x_x_y_pxy.lean) |
| 3929 | 1429 | `B` | [Le_3929_pyx_y_pyx_x_x_y_pyx](../equational_theories/Definability/Le_3929_pyx_y_pyx_x_x_y_pyx.lean) |
| 4343 | 817 | `A` | [Jb_4343_pxy_x_pxy_y_y_x_pxy](../equational_theories/Definability/Jb_4343_pxy_x_pxy_y_y_x_pxy.lean) |
| 4439 | 817 | `A` | [Lc_4439](../equational_theories/Definability/Lc_4439.lean) |
| 4470 | 817 | `B` | [Jb_4470](../equational_theories/Definability/Jb_4470.lean) |

All existing finite declarations and proof files remain unchanged. The
catalogue imports the 38 original proof modules; their now-redundant direct
imports were removed from `Definability.lean`. Every one of the previous
13,327 reachable local modules is retained; the two new modules bring the
total to 13,329.

## Board effect

Compared with the immediately preceding square-swap snapshot, these results
prove **6,420 additional raw structural/all pairs**, resolving **705 old
structural class cells**. All 1,547 candidates from the scanned family are now
covered by closure. No negative counts or other relation-status counts change.

Two pairs of old structural/all classes merge: **{8, 307}** and **{11, 312}**.
Thus the number of classes falls from 739 to 737. Remaining open raw pairs fall
from 450,972 to **444,552**, and the remaining quotient from 61,950 to
**60,586** open cells. The quotient decrease of 1,364 must not be presented as
1,364 solved questions: 705 old cells were settled, while the other 659 are
coalesced representations after class merging.

The full [remaining-cell audit](definability_open_audit.md) and all generated
appendices have been refreshed. Cross-relation profiles change where S/all
became positive, even though the other nine relations' own statuses do not.

## Verification

With dependencies cached, the shared core compiled in 3.8 seconds and the
47-result catalogue, including axiom and rejection checks, in 5.1 seconds
(6.57 seconds including Lake overhead for the catalogue command). These are
local incremental timings, not cold-build benchmarks.

The full incremental `Definability` build passed in **104.93 seconds** (16,630
jobs considered). The exhaustive source scan, closure, full-matrix comparison,
class-rectangle checks, and regenerated inventory passed in **201.70 seconds**.
The ten Python regression tests and import-minimality/coverage check also pass.
