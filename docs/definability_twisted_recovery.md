# Twisted finite models obstruct term recovery

17 September 2026. Three finite countermodels settle three more rows of the
[completely-open table](definability_open/completely_open.md):

| Source → target | Carrier | Source coefficients `(A,B)` | Twist `χ(d)` | Family size | Target parameters `(a,b,c)` |
|---|---|---|---|---:|---|
| 1076 → 1313 | F₅ × F₁₃ | (4,7) | Quadratic character of F₅ | 845 | (2,7,0), (2,9,0) |
| 1516 → 1489 | F₅ × F₇ | (3,6) | 0 at zero, 1 elsewhere | 245 | (3,6,0) |
| 1685 → 3548 | F₇ × F₅ | (2,3) | Quadratic character of F₇ | 175 | (6,2,0) |

Each conclusion is **negative in TS/fin, hence TS/all**. This pass left the other
six definability variants open. In particular, the displayed
target operations exist in the containing family; the obstruction concerns
recovering the source operation by a term.

**Update, 20 September 2026:** a different, 49-element witness upgrades
**E1076 → E1313 to a one-way FO-definability negative**, closing all eight
definability variants for its four raw pairs. See the
[finite-symmetry pass](definability_finite_symmetry.md). The other two rows still
have only the term-structural negatives established here.

[TwistedRecovery.lean](../equational_theories/Definability/TwistedRecovery.lean)
contains the shared argument and all three certificates. All three conclusions
have axiom guards listing only `propext`, `Classical.choice`, and `Quot.sound`.
The finite arithmetic checks use kernel `decide`, with no native-computation
axioms, solver certificates, or pending hypotheses.

## The family and its closure

For the primes `p,q` and character `χ` in the table, write

```
F(a,b,c)((x,u),(y,v)) =
  (a*x + (1-a)*y, b*u + (1-b)*v + c*χ(x-y)).
```

The first coordinate lies in Fₚ and the second in F_q. The source is
`F(A,B,1)`. The character values, in residue order, are

```
F₅ → F₁₃:  [0, 1, -1, -1, 1]
F₅ → F₇:   [0, 1,  1,  1, 1]
F₇ → F₅:   [0, 1,  1, -1, 1, -1, -1].
```

Each character is multiplicative, including at zero. Consequently, with
`w(x,y) = χ(x-y)`,

```
w(a*x + (1-a)*y, a'*x + (1-a')*y) = w(a,a') * w(x,y).
```

The projections are `F(1,1,0)` and `F(0,0,0)`. Composing two family members
along the source gives another member, with parameters

```
a'' = A*a + (1-A)*a'
b'' = B*b + (1-B)*b'
c'' = B*c + (1-B)*c' + w(a,a').
```

This proves that **every binary term of the source belongs to the family**.
It is a containment argument: the Lean proof does not need to enumerate the
exact clone or prove that every parameter triple is reachable.

## Why recovery fails

The target law forces `c=0`. For E1489, its instance at
`x=(1,0), y=(0,0)` suffices. For E1313 and E3548, add the instance at
`x=(0,1), y=(0,0)`. Lean checks these implications over all parameter triples.
The complete target-parameter lists above are also independently checked by
evaluating the full target laws in Python; only `c=0` is needed in Lean.

When `c=0`, the operation preserves the subset `Fₚ × {0}`. Every term of
an operation preserving a subset preserves it too. The source fails this
property: multiplying suitable `(x,0)` and `(y,0)` gives a second coordinate
`χ(x-y) ≠ 0`. Thus no target operation term-defined from this source can
term-define the source back.

This uses one explicit finite source model per row. It permits the forward
and recovery terms to depend on that model, exactly as the definability
definitions allow.

## Board impact

The completely-open inventory falls **60 → 48 raw pairs**, or
**16 → 13 TS/all class pairs**. The twelve removed pairs are exactly

| Source class | Target class | Raw pairs |
|---|---|---:|
| {1076, 2531} | {1313, 2294} | 4 |
| {1516, 2091} | {1489, 2098} | 4 |
| {1685, 1922} | {3548, 3954} | 4 |

No positive equivalence classes merge. Removing these pairs from the
completely-open table settles their two TS statuses, not all eight statuses.
TS/all open cells fall 25,519 → 25,507 and TS/fin open cells fall
23,479 → 23,467. All other boards' own statuses are unchanged.
The outstanding E1486 → E1485 search-certificate gap is unchanged; see the
[central-spectrum evidence status](definability_central_spectrum.md).

## Reproduction

```sh
lake build equational_theories.Definability
python3 scripts/definability_twisted_check.py
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_audit.py --write --date 2026-09-17 --verify-closure
OPENBLAS_NUM_THREADS=2 python3 -m unittest discover -s scripts -p 'test_definab*.py'
python3 scripts/definability_imports.py --check
```

The independent checker uses only the displayed formulas and the repository's
equation definitions. It verifies source satisfaction on all assignments,
the interpolation identity, and every target member of each parameter family.
It neither reads the historical private model bank nor writes proof facts.
The board instead extracts the three imported Lean declarations and computes
their closure.

The standalone proof module checked in **66.48 seconds**. The full incremental
Definability build passed (**16,642 jobs, 188.92 seconds**, concurrently with
the audit), as did all **21** regression tests and the import check. The entry
point has 6,580 direct imports and retains all 13,341 reachable local modules.
Audit regeneration passed in **210.34 seconds**, including agreement of all
ten negative propagations with the full-matrix reference calculation.
