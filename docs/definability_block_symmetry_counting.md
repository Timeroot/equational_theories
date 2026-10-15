# Compactness counts for finite-group blocks and a shared fixed point

Date: 2026-10-13. **The 79 new negative arrows are formalized in Lean.**
This extends the [independent pair-swap argument](definability_fo_counting_followup.md).
The starting checkpoint is the audit with source fingerprint
`4a69b7bf6eedf5133ecd921d0d2d3ad352429227acb252fd3b1a147e8307597f`,
after the earlier 63-negative pass. Results here are additional to that pass.

All arrows below are **source → target**, in the **unrestricted FO-structural**
sense. They rule out parameter-free FO definitions with parameter-free recovery
on arbitrary magmas. They do not by themselves refute finite-only structure or
one-way definability.

## Why these are legitimate restricted counts

The existing `FORecoveryCompactness.bounded_restricted_counts` theorem says
that an unrestricted FO-structural arrow A → B supplies a constant K bounding
the number of source tables by K times the number of target tables, within
any family preserved by parameter-free definitions. The same K works for every
carrier and every such family. Prescribed automorphisms give a suitable family.
An arbitrary algebraic condition, such as commutativity or idempotence, cannot
simply be imposed on both counts: forward FO definitions need not preserve it.

Independent group actions give families whose size grows exponentially with
the number of blocks. An excess in a small local count then contradicts the
uniform K. The source and target operations need not choose the same formulas
on different models; compactness is what makes the multiplier uniform.

## Regular actions of arbitrary finite groups

Let H be a nontrivial finite group, of order n, and let the carrier be I × H,
with m blocks. Prescribe every independent left translation in each block.
No commutativity assumption on H is needed.

An invariant product of two elements of the same block stays in that block:
otherwise translating its output block would fix both inputs and move the
output. Within a block it has the unique form

```text
f(a,b) = a * p(a⁻¹ * b),       p : H → H.
```

For two different blocks, it chooses an element of one of the input blocks,
with a fixed right offset. There are 2n choices per ordered pair of blocks.
Every unary term stays in its original block. If c_H(A) is the number of local
functions p satisfying unary law A, the exact invariant-table count is

```text
c_H(A)^m · (2n)^(m(m−1)).
```

Thus c_H(A) > c_H(B) > 0 refutes A → B. The factor between blocks cancels.
Both the exact parameterization and the counting criterion are proved in
[RegularBlockCounting.lean](../equational_theories/Definability/RegularBlockCounting.lean),
`invariantEquiv`, `invariant_count`, and `not_structural`. Equivariance reduces
the local law check to the identity element of H.

The survey counted cyclic groups C2 through C6, the Klein four group V4, and
S3. Relative to the starting audit, four groups suffice for all 70 new regular
block negatives:

| Group | Local functions enumerated | Additional explicit arrows assigned to this group |
|---|---:|---:|
| C3 | 27 | 48 |
| C4 | 256 | 7 |
| V4 | 256 | 12 |
| C5 | 3,125 | 3 |

The assignments avoid duplicates; the same arrow can have several group
witnesses. The C6 and S3 counts gave no further arrows in this survey. The
*general* Lean theorem nevertheless covers noncommutative groups too.
Only counts needed for the exported arrows are formalized; the other survey
counts remain Python calculations, not additional Lean claims.

For example, C3 gives c(E8)=15 and c(E99)=11, refuting E8 → E99. V4 gives
c(E99)=136 and c(E8)=112, refuting the reverse direction. Different small groups
can therefore prove both directions false.

Every negative is explicitly stated in
[RegularBlockCountingCatalogue.lean](../equational_theories/Definability/RegularBlockCountingCatalogue.lean),
with name `Equation<Target>_not_StructuralFrom_Equation<Source>_regularBlocks<Group>`.
The imported `RegularBlockCountsC3`, `C4`, `V4`, and `C5` modules contain the
individual kernel-checked counts.

## Allowing a shared fixed point

The regular family has a limitation: unary terms cannot leave their free orbit.
Add a single point ∞, fixed by every block action, and keep the independent
translations on I × H. Now a unary term can reach ∞.

The shared point necessarily satisfies ∞·∞=∞. In each block there are three
local parameters:

- p : H → H ∪ {∞}, describing products within the free orbit;
- u ∈ H ∪ {∞}, describing a·∞ by translating u by a;
- v ∈ H ∪ {∞}, describing ∞·a by translating v by a.

An output for inputs from different blocks lies in either input block or at ∞,
giving 2n+1 choices. If d_H(A) counts the local parameter triples satisfying A,
the exact count is

```text
d_H(A)^m · (2n+1)^(m(m−1)).
```

The local root satisfies every unary law automatically. It again suffices to
check one free point. The full construction, inverse, count, and compactness
argument are formalized in
[PointedBlockCounting.lean](../equational_theories/Definability/PointedBlockCounting.lean).

This gives nine further arrows that none of the surveyed regular groups supplied:

| Group and source | Newly refuted targets | Local source count | Local target counts |
|---|---|---:|---|
| C2, E3659 | E99, E614, E817, E1020, E1223, E1426, E4380 | 54 | 45, 32, 36, 50, 47, 45, 45 |
| C2, E4380 | E817 | 45 | 36 |
| V4, E1629 | E3253 | 10,500 | 9,625 |

These are stated in
[PointedBlockCountingCatalogue.lean](../equational_theories/Definability/PointedBlockCountingCatalogue.lean),
with names ending in `pointedBlocksC2` or `pointedBlocksV4`.
The local calculations enumerate 81 and 15,625 parameter triples respectively.
The number of blocks is arbitrary; no large magma tables or SAT certificates
are enumerated or stored.

## Why the fixed point matters: E817 versus E4380

The following explanation is a pen-and-paper observation; the general equality
of the two regular counts has **not** been separately formalized. The pointed
negative E4380 → E817 itself is fully formalized.

Write d=p(1). For E817, the local condition is p(d²)=1. For E4380 it is
p(d)=d*p(d⁻¹). If d=1, either law allows n^(n−1) choices. If d is a nonidentity
involution, either condition is impossible. For every remaining d, either law
allows n^(n−2) choices: E817 fixes one additional coordinate, while E4380 relates
two distinct additional coordinates and leaves one of them free. Consequently,
for **every** finite group H of order n≥2, both regular counts equal

```text
n^(n−1) + (n − #{d : d²=1}) · n^(n−2).
```

No choice of a regular finite group can distinguish these two laws by this
count. Allowing the shared fixed point breaks that equality: for C2, the counts
become 45 and 36. Likewise E3659 can now have a square map that retracts onto
the shared point, instead of being forced to act invertibly on a free orbit.

## What other transitive actions can add

This is a further pen-and-paper observation, not yet formalized in Lean. For
unary-law counts, an independent transitive action on a non-singleton block
reduces to a regular action on a smaller group, up to a factor independent of
the law. Thus nontransitive actions, such as the shared fixed point above, are a
natural next source of additional information.

Write a finite transitive permutation action as Γ/K. The points fixed by the
stabilizer K of the base point are exactly N_Γ(K)/K: finiteness turns the
condition g⁻¹Kg ⊆ K into equality. Set C=N_Γ(K)/K. Every unary term evaluated at
the base point remains in this fixed-point set, on which C acts regularly.
The equivariant table entries there have exactly the regular-C parameters.
Every other orbit of ordered pairs has independent output choices fixed by
its stabilizer, contributing a factor T that does not depend on the unary law.
Hence the local A-count is T·c_C(A). Between two independent blocks, the output
must be an equivariant unary map into one input block; there are 2|C| choices.
The amplified count is therefore

```text
(T·c_C(A))^m · (2|C|)^(m(m−1)).
```

The T factor cancels in every comparison. When C is trivial, every invariant
operation is idempotent, so these actions distinguish no unary laws at all.
This observation is specific to independent transitive blocks and unary laws;
it is not a claim that all possible automorphism restrictions have been exhausted.

## Complete separation among the one-variable laws

There are 31 laws in the catalogue involving only one variable. Their existing
unrestricted FO-structural positive arrows group them into the following 17
classes. The new proofs settle all 32 previously unresolved equivalence pairs
among these classes. Consequently this restricted equivalence classification is
now complete: every two different rows have a refuted direction.

| Representative | One-variable laws in this class |
|---:|---|
| E1 | E1 |
| E3 | E3 |
| E8 | E8, E23, E307, E359 |
| E47 | E47, E255 |
| E99 | E99, E203 |
| E151 | E151 |
| E411 | E411, E3050 |
| E614 | E614, E2847 |
| E817 | E817, E2644 |
| E1020 | E1020, E2441 |
| E1223 | E1223, E2238 |
| E1426 | E1426, E2035 |
| E1629 | E1629, E1832 |
| E3253 | E3253, E4065 |
| E3456 | E3456, E3862 |
| E3659 | E3659 |
| E4380 | E4380 |

This statement concerns equivalence among these 31 laws. It does not say that
all directed arrows between their classes are settled, nor that the rows cannot
merge with other classes containing no one-variable representative. The
finite-only FO-structural classification remains a separate question.

## Reproduction and proof checking

[scripts/definability_regular_block_counts.py](../scripts/definability_regular_block_counts.py)
reproduces the exploratory counts and selects arrows open in the current audit.
[data/definability_regular_block_counts.json](../data/definability_regular_block_counts.json)
records the starting audit fingerprint, regular and pointed counts, and selected
arrows. Rerunning selection after updating the audit will naturally find fewer
open arrows. Python output is not used as a proof oracle.

All 79 exported results have axiom guards allowing only `propext`,
`Classical.choice`, and `Quot.sound`. There are no sorries, native-decide axioms,
or external proof certificates in the new arguments. The small local count
lemmas use `decide +kernel`; the amplification to arbitrarily many blocks is
symbolic. The largest count modules took approximately 52 seconds (C5) and
46 seconds (pointed V4) in the final build, with dependencies already built.


## Propagated impact and validation

The final audit found the following additional unrestricted FO-structural
negatives, relative to the checkpoint after the pair-swap pass:

| Measure | Before | After | Resolved |
|---|---:|---:|---:|
| Open raw directed equation pairs | 440,912 | 440,583 | 329 |
| Open directed pairs of current classes | 59,785 | 59,684 | 101 |
| Possible equivalence-class mergers | 904 | 853 | 51 |

The 79 explicit declarations are distinct arrows that were open at the starting
checkpoint. The propagated counts above are deduplicated. Of the 51 equivalence
separations, 32 complete the one-variable classification described above.
There are still 737 proved classes globally; these results establish separations,
not new positive class collapses. All other relation boards remain unchanged.
In particular, finite FO structure still has 1,047 unresolved class pairs.

Both catalogues and all axiom guards passed, and the full
`lake build equational_theories.Definability` passed (17,259 jobs).
The ten quotient propagations were independently compared against full-matrix
propagation by `definability_audit.py --write --verify-closure --date 2026-10-13`.
The local Lean count statements were also compared with the independent Python
counts. The new Lean sources total 77,837 bytes (about 76 KiB).

Final audited source fingerprint:
`44a9aeb7ab167b2bef517b04435edf82de1ff7235d9725e9374fd846d96349d9`.
The [FO-structural priorities](definability_structural_equivalence_gaps.md) and
[term-structural inventory](definability_term_structural_equivalence_gaps.md)
are refreshed against this same snapshot.

## Finite term-structural follow-up

The [noninvertible-map follow-up](definability_unary_tail_counts.md) finds 31
additional finite term-structural negatives using maps with tails feeding into
cycles. Its finite product argument bypasses compactness. The earlier 79 arrows
here were already known negative in that mode; the new arrows use different
families and source laws.
