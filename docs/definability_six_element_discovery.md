# Six-element recovery obstructions, 14 October 2026

This pass follows [the generation and cube-companion pass](definability_generation_discovery.md).
It adds 38 direct finite term-structural refutations, using four six-element
magmas. These also refute the corresponding unrestricted term-structural
arrows. They do not, by themselves, refute FO-structural or term-definable
arrows: a companion may exist, but it cannot recover the original operation by
a term.

## Audited effect

The [progress record](../data/definability_six_element_discovery.json) compares
this pass with the snapshot immediately after the generation/cube pass.
Closure settles the same 481 directed equation pairs negatively in each
term-structural variant, plus four unrestricted FO-structural arrows positively.

| Board | Open before | Open after | Newly resolved |
|---|---:|---:|---:|
| Unrestricted term-structural | 21,193 | 20,712 | 481 negative |
| Finite term-structural | 19,327 | 18,846 | 481 negative |
| Unrestricted FO-structural | 421,800 | 421,796 | 4 positive |

Finite and unrestricted negative counts overlap; they are not 962 different
equation pairs. The other seven boards are unchanged, as are all known
class partitions and remaining possible mergers. These are new directional
results between already separated classes. In particular, the term-structural
possible-merger counts remain 28 unrestricted and zero finite, and the
FO-structural counts remain 604 unrestricted and 1,047 finite.

**The E72 target column is now completely settled in both term-structural
variants.** Its last open source class was E960.

The full Lean build passed (17,317 jobs), and all ten closure computations
matched the independent full-matrix reference. The equivalence-gap inventories
were regenerated from the same verified relations. No new proof uses `sorry`,
`native_decide`, or a nonstandard axiom.

## E960: a small arithmetic family

[SixElementCloneRecovery.lean](../equational_theories/Definability/SixElementCloneRecovery.lean)
works on two copies of the field with three elements. Write a point as `(p,a)`,
with `p` a bit and `a` in `ZMod 3`. Define

```
(p,a) * (r,b) = (r, a-b+1)  if p=1 and r=0,
               (r, b+1)    otherwise.
```

This satisfies E960, `x = y*((z*y)*(x*x))`. Its square permutation is
`σ(p,a)=(p,a+1)`. A family of just 36 binary operations contains the projections
and is closed under composition along `*`, so it contains every binary term
operation. A family member chooses one argument `v` and calls the other `u`.
It preserves the bit of `v`, translates its field coordinate by `k` outside
the rectangle where `u` is odd and `v` is even, and inside that rectangle either
translates by `l` or reflects to `u-v+l`. There are two choices of argument,
three choices each of `k` and `l`, and two choices of reflection.

The composition formula is proved by parity cases and ring arithmetic. When
the two inner operations choose the same argument, their composite increases
the second operation's two translation parameters by one. When they choose
different arguments, the outside parameter still increases by one, the inside
parameter becomes `k₁-l₂+1`, and reflection toggles. No exhaustive multiplication
table is needed for this proof.

If `k=0`, the operation is idempotent. If reflection is disabled, it commutes
with `σ`. Either property is inherited by every term operation of that
companion. The source has neither property. Consequently only the twelve
parameters with `k≠0` and reflection enabled can possibly recover the source.
One explicit assignment refutes each target law for each of those twelve
parameters. This proves E960 cannot term-structurally produce any of:

```
55, 65, 669, 679, 713, 825, 845, 872, 1434, 1451, 1525,
3315, 3316, 3318, 3319, 3518, 3519, 3521, 3522, 4275, 4320.
```

All numbers here denote target equations. Additional targets follow from
ordinary implication and duality. The final symbolic module built in about
22 seconds in this session; the initial table-based version took about
three minutes and was replaced. The kernel checks the arithmetic and all 252
small counterassignments. There is no `native_decide`, LRAT file, or `sorry`.

## A separate, more conceptual E960 → E72 obstruction

[SixElementCyclicRecovery.lean](../equational_theories/Definability/SixElementCyclicRecovery.lean)
proves the E72 refutation without enumerating the binary clone. Every unary
term of the source is one of `id`, `σ`, and `σ²`. Thus a term companion's square
map is one of these three maps. The identity option makes the companion
idempotent, preventing recovery of the non-idempotent source.

For either other square map `d`, E72 says that every left row `f` satisfies
`f²d=id`. Since `d³=id`, this implies that `f` commutes with `d`, and hence
with `σ`. Each row is therefore determined by its values on one point of each
three-cycle. Its diagonal value and E72 then force it to equal `d`. That final
step is a 432-case kernel check (two orientations, six row labels, and 36
choices of the two entries). All rows coincide, so every companion term
ignores an argument; the original operation depends on both. This module
built in about four seconds.

## E4541 and E1037: recovery cannot enlarge the permitted range

[SmallCloneRanges.lean](../equational_theories/Definability/SmallCloneRanges.lean)
uses the following general invariant. Fix a subset `S` and consider operations
that are either a projection or have their entire image in `S`. If a magma's
operation has this property, all its term operations have it: composition
along a projection chooses one subterm, and composition along a map into `S`
again lands in `S`.

Three archived six-element models have especially small binary clones:

| Source | Operations in the family | Restricted image set | Direct targets |
|---|---:|---|---|
| E1037 | 4 | Empty | E3529 |
| E4541, first model | 9 | `{3,5}` | E4283, E4290, E4358, E4364, E4369, E4396, E4398, E4512, E4515, E4531 |
| E4541, second model | 12 | `{3,4,5}` | E4320, E4362, E4435, E4482, E4544 |

In each family only the original operation and its opposite escape the range
invariant. Both fail the listed targets, as witnessed by two concrete
assignments per target. The original source escapes the invariant, so it
cannot be recovered from any target companion. In particular, **E4541 cannot
be converted term-structurally to an associative magma (E4512), even on finite
carriers**. The combined module built in about 50 seconds.

## Reproduction and research inventory

```
python3 scripts/definability_six_element_clone.py --check
python3 scripts/definability_small_clone_ranges.py --check
lake build equational_theories.Definability
```

Both generators reproduce their Lean output or generated section byte for
byte. Every public negative declaration has a standard-axiom guard.

[The saved model inventory](../data/definability_six_element_clones.json) also
contains other small complete binary clones found in the archived six-element
bank. Their `negative_pairs` are computational research results, **not a list
of Lean theorems**. Only the declarations in the modules above should be used
as new certified edges. This preserves the remaining 32-, 36-, and 48-operation
examples for further work.

[DiagonalTranspose.lean](../equational_theories/Definability/DiagonalTranspose.lean)
provides a second general construction: keep or transpose an input pair
according to a symmetric Boolean combination of equalities between inputs,
squares, and iterated squares. The square map survives, so the rule is unchanged
and applying it twice recovers the operation. The involution and its
FO-structural interpretation are formalized. Candidate source/target arrows
still require their own target-law proofs; surviving a finite model bank is
not sufficient.

## A new unrestricted FO-structural arrow

[DiagonalTransposeCatalogue.lean](../equational_theories/Definability/DiagonalTransposeCatalogue.lean)
proves **E3545 → E3253** for arbitrary carriers. The rule is particularly simple:
keep `a*b` if `a*a=b*b`, and use `b*a` otherwise. This preserves every square,
so it preserves its own branching condition and is an involution. The source
law `x*y = x*((z*y)*x)` then gives the target law
`x*x = x*(x*(x*x))` for the transformed operation. Lean proves that implication
for arbitrary source models; the catalogue module built in about seven seconds.
The finite FO-structural arrow was already known, while the unrestricted arrow
was open. The corresponding term-structural arrows remain open.

This establishes a recoverable companion for each source model. It does not
assert that every E3253 model is the image of an E3545 model, or that the two
theories have equal model counts.

The search tried 67 square-based symmetric guards, first screened against all
models of orders two and three and then against archived larger models.
397 distinct candidate arrows survived that screening. Only this one received
a target-law proof in the bounded Lean search; failed searches and timeouts are
not recorded as refutations.

A further [parity-family argument](definability_six_element_parity_route.md)
gives a compact pen-and-paper route to the E117 → E411 and E1453 → E411
refutations in that research inventory. It describes the shared 36-operation
family by four parameters and reduces E411 to preservation of parity fibres
or dependence on just one argument. That argument is explicitly awaiting Lean
formalization and is not included in the certified-edge counts above.
