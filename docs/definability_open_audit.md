# Audit of the remaining definability cells

Snapshot: **16 September 2026**, equations E1–E4694. This audits all five
relations, over arbitrary and finite carriers separately. It is an exhaustive
inventory of what the current source-derived board leaves unresolved, not a
claim to have searched the mathematical literature for every pair.

Start with the totals below, then use the linked inventories for the complete
lists. Each inventory includes every open pair of equivalence-class
representatives, all class memberships, and the other relations' statuses at
the representative pairs. Thus the inventories specify **every raw open cell**,
not just a shortlist or the first few results of a search.

For a single cross-board progress metric, start with
[completely_open.md](definability_open/completely_open.md): **180 raw pairs /
43 TS/all class pairs** remain open in all eight definability variants at once.
Its four closure-impact columns measure how many of those raw pairs would stop
being completely open after a positive or negative result in TS/all or D/fin,
including transitive consequences and negative propagation. These hypothetical
impacts overlap and are not additional proved results.
In this snapshot the two positive columns agree for every row, even after
including negative propagation; the negative columns can differ substantially.
For example, `467 → 917` and `467 → 1729` both have impacts **12, 12, 4, 12**
in the table’s column order. The largest remaining positive impact is **32 of
180** pairs, for `1276 → 692`. The earlier leaders `477 → 1073` and
`1492 → 1073` are now TS/all-refuted, though still open in the other seven variants.
The [spectrum recheck](definability_spectrum_check.md) separately tests whether
completed spectrum theorems supply any missing finite-FO negatives.

## 1. What a cell means

Throughout, **source → target** means “every magma satisfying the source admits
the target structure on the same carrier.” Lean writes the target first:
`56 → 50` in the structural board is `Law50.StructuralFrom Law56`.

| Relation | Required target operation |
|---|---|
| `implies` / I | The original operation already satisfies the target. |
| `termStructural` / TS | A term-defined operation, with the original operation term-definable back from it. |
| `structural` / S | A parameter-free first-order definable operation, with parameter-free first-order recovery. |
| `termDefinable` / TD | A term-defined operation; no recovery required. |
| `definable` / D | A parameter-free first-order definable operation; no recovery required. |

`all` quantifies over arbitrary carriers; `fin` only over finite carriers.
Neither means “tested through some size.” The definitions put the source magma
*before* the existential choice of a term or formula: the witness may depend on
the magma. A single uniform term/formula is sufficient but is not required.
See [Basic.lean](../equational_theories/Definability/Basic.lean) and
[FiniteFlavour.lean](../equational_theories/Definability/FiniteFlavour.lean).

The hierarchy is I ⇒ TS ⇒ S ⇒ D and TS ⇒ TD ⇒ D, with `all ⇒ fin`
for each relation. S and TD are not interchangeable. In particular, separately
knowing S and TD does not prove TS: they may use different target operations,
and FO recovery need not be term recovery.

`P` / PROVED and `N` / REFUTED mean established by extracted seeds and their
closure. `O` / OPEN means neither was obtained. These are **board statuses**;
the extraction is not itself a Lean proof or a complete recognizer of Lean
theorems.

## 2. Complete coverage and how to read it

Each raw grid contains 4,694 × 4,693 = **22,028,942** off-diagonal directed
pairs. Self-cells are reflexively positive. For a particular relation and
flavour, two equations are put in the same class exactly when that board has
positive arrows both ways; the representative is the least equation number.
The quotient is relation-specific and flavour-specific.

| Relation | Open raw pairs, all | Open class pairs, all | Open raw pairs, finite | Open class pairs, finite |
|---|---:|---:|---:|---:|
| Implication | 0 | [0](definability_open/implies_all.md) | 2 | [2](definability_open/implies_fin.md) |
| Term-structural | 25,639 | [5,236](definability_open/termStructural_all.md) | 23,583 | [4,709](definability_open/termStructural_fin.md) |
| Structural | 444,552 | [60,586](definability_open/structural_all.md) | 408,802 | [53,983](definability_open/structural_fin.md) |
| Term-definable | 1,326 | [273](definability_open/termDefinable_all.md) | 2,310 | [232](definability_open/termDefinable_fin.md) |
| FO-definable | 3,994 | [662](definability_open/definable_all.md) | 3,523 | [332](definability_open/definable_fin.md) |

The [generated totals](definability_open/summary.md) also give positive,
negative, and class counts. Do not add columns or relations and call the sum
independent mathematical questions: hierarchy, transitivity, duality, and the
two carrier flavours couple them. Even distinct quotient cells are not an
independent or minimal basis of unsolved problems.

Since the 15 September snapshot, the [square-swap pass](definability_reversible.md)
settled **24 structural/all class pairs (100 raw pairs)**. The subsequent
[argument-swap pass](definability_argument_swap.md) settled **705 further old
class pairs (6,420 further raw pairs)**. Both extend finite constructions to
arbitrary carriers. Argument swapping also merges the old class pairs
{8, 307} and {11, 312}; the larger drop in the quotient count includes merged
representations and is not a count of independent questions solved. Those two
passes left other relations' own statuses and all negative counts unchanged.

The later [Gaussian recovery pass](definability_gaussian_recovery.md) proves
three TS/all negatives from E1496, targeting E1113, E680, and E1682. Their
closure settles **104 raw pairs / 18 TS/all class pairs**, all previously
completely open: **284 → 180 raw**, **61 → 43 reduced**. No positive classes
merge, and all other boards' statuses are unchanged. In particular, the finite
questions for those 104 pairs remain open. The guide lists every affected
class pair and explains the shared infinite countermodel.

In an inventory, `s → t` expands to `class(s) × class(t)`. This is lossless:
both positive and negative statuses are constant on each class rectangle, so
the open status is too. The generator checks this entry-by-entry on the full
matrices, checks the class partition, and checks the weighted raw-open total.
Ranges such as `63–65` mean exactly `63, 64, 65`, not an approximate block.

Each listed pair has a ten-character profile, in this order:

```text
I/all I/fin  TS/all TS/fin  S/all S/fin  TD/all TD/fin  D/all D/fin
```

For example, `NNOOPPPPPP` says implication is refuted in both flavours,
term-structural definability is open in both, and the other six cells are
positive. This is the current profile of both `56 → 50` and `440 → 414`.

**Only the named relation's status is guaranteed uniform on its class
rectangle.** The other nine profile characters describe the representative
pair, not necessarily all its class members. Each appendix therefore gives
both a representative-profile histogram and an independently computed
raw-profile histogram; weighting the first is not a substitute for the second.

The machine-readable [snapshot](definability_open/snapshot.json) contains the
same inventory, class partition, exact raw-profile counts, finite/all cross-tabs,
historical shortlist, and complete extraction diagnostics. It is generated
documentation, **not a new source of proof facts**, and nothing in Lean or the
board calculation imports it.

## 3. What sort of work remains?

These are methods suggested by the *status* of a cell, not assertions that the
suggested proof exists or is easy. The full profile lists in the appendices
assign every open representative pair to a precise combination of known and
unknown relations.

| Situation at a pair | What is still missing | Relevant existing infrastructure |
|---|---|---|
| TS open, S and TD positive | A target admitting term recovery, not merely FO recovery or a separate term witness. | [Subclone](../equational_theories/Definability/Subclone.lean) for obstructions; [Parastrophic](../equational_theories/Definability/Parastrophic.lean) for reversible terms. |
| S open, D positive | Preservation/recovery of the original operation. | [AutBox](../equational_theories/Definability/AutBox.lean) on finite carriers; [Reversible](../equational_theories/Definability/Reversible.lean) and [RowCycle](../equational_theories/Definability/RowCycle.lean) for explicit recovery on all carriers. |
| D open, TD refuted | Any positive solution must go beyond terms on at least one source model. | [FiniteBridge](../equational_theories/Definability/FiniteBridge.lean), FO symmetry certificates, or genuinely quantified definitions. |
| TD open | Either a term construction or an obstruction to **all** terms. | [Clone](../equational_theories/Definability/Clone.lean), [LinearInt](../equational_theories/Definability/LinearInt.lean), and term witnesses. |
| `all` open, `fin` positive | Extend the finite result, or find an infinite obstruction. | Examine the finite proof's use of injective/surjective equivalence and automorphism invariance. |
| `all` refuted, `fin` open | The infinite obstruction does not settle the finite question. | Finite witnesses or a theorem for every finite carrier; more infinite counterexamples do not close this cell. |
| D open in both flavours | Even existence of a definable target has not been settled. | Automorphism-invariant operation families, finite clone/symmetry certificates, and spectrum obstructions where available. |

### The large structural remainder

The structural boards are by far the largest inventories. A term construction
can deliberately discard information, whereas a structural construction must
retain enough to recover the original operation. Thus completing TD does not
automatically complete S. Conversely, a clone obstruction to TD does not
automatically refute S, because S permits non-term definitions.

This distinction accounts for most of the actual remainder: **441,691 of
444,552** raw open S/all pairs already have a TD/all proof. Conversely,
**2,268** raw open TS/all pairs already have both S/all and TD/all proofs.
On the weakest finite board, **1,278 of 3,523** raw open D/fin pairs have
TD/fin refuted: further term search cannot settle those pairs positively.
These counts come from the raw-profile histograms, not representative weights.

For a **fixed finite** source magma, FO definability is equivalent to invariance
under its automorphisms. Structural definability can then be tested by seeking
a target operation with exactly the same automorphism group. This equivalence
is proved in `FiniteBridge`; equality of automorphism groups alone is **not** a
sufficient replacement for mutual FO definability on arbitrary infinite magmas.
Nor does checking every source model up to order k prove a `FromFin` theorem.

The appendices rank the largest open source blocks as entry points for work
that might solve many targets at once. Those rankings are counts of currently
open target classes, **not predicted gains**: a new result can propagate to
other rows or merge classes, and a failed construction proves nothing.

### Finite and arbitrary questions must be kept separate

The [finite/all cross-tab](definability_open/summary.md#arbitrary-versus-finite-carriers)
compares the *same raw equation pairs*, avoiding mismatched quotient
representatives. It distinguishes O/O, O/P, N/O, and N/P. The last is a settled
finite/infinite distinction, not an open cell. P/O, P/N, and O/N cannot occur
after hierarchy closure.

The finite TD board can have **more raw open cells** than the arbitrary TD
board: an infinite counterexample refutes `all` without refuting `fin`. Its
smaller quotient can simultaneously have fewer reduced open cells. Neither
phenomenon is a counting error.

For negatives, first ask what invariant the desired relation must preserve.
Terms preserve more than FO definitions do. A bounded search finding no term
does not certify a clone obstruction; a complete closed family does. Failure
of one proposed companion is not non-definability. An order n with a source
model but **no** target model is stronger: it refutes even finite FO
definability and hence all stronger relations. The direction here is
`spectrum(source) ⊆ spectrum(target)` for a positive source → target arrow.
The helper `not_definableFrom_of_no_fin_model` is in
[Negative.lean](../equational_theories/Definability/Negative.lean). Spectrum
inclusions themselves are not an eleventh board in this audit.

### The two finite implication cells

The entire remaining implication inventory is **`677 → 255` and
`2910 → 47`**. They are duals, hence one mathematical question presented in
two orientations, not two independent problems. The first asks whether, on
finite magmas,

```text
E677: x = y ◇ (x ◇ ((y ◇ x) ◇ y))
  implies
E255: x = ((x ◇ x) ◇ x) ◇ x.
```

The [E677 commentary](../commentary/Equation677.md) explicitly calls this
finite implication open and links its discussion; the
[blueprint chapter](../blueprint/src/chapter/677.tex) develops the problem.
This is a documented open problem in the project's mathematical exposition,
not merely an inference from missing code. No fresh literature-wide status
check is asserted here. The arbitrary-carrier implication is already refuted.
The two cells have profile `NOOOOPPPPP`: finite structural definability and
arbitrary term/FO definability are positive, while term-structural definability
is still open in both flavours. Solving a weaker companion problem would not
by itself settle this implication question.

## 4. Rechecking the old shortlist

The historical [status report §3.5](definability_status.md#35-all-35-open-cells-the-commentary-predicts)
listed 35 relation/flavour cells, not the whole board. Every one has been
requeried; the [complete updated table](definability_open/summary.md#historical-shortlist-rechecked)
retains its original relation and includes all ten current statuses. Do not
reuse the historical description “open in every flavour.”

Of those 35 cells, **31 remain open, two are proved, and two are refuted**.

Two particularly important corrections:

- **`56 → 50` and `440 → 414`: structural is proved over all magmas**, hence
  also finite magmas, by the reversible row-cycle constructions in
  [RowCycle.lean](../equational_theories/Definability/RowCycle.lean).
  Their term-structural questions remain open in both flavours. This is a
  restriction-on-terms question now, not missing FO recovery.
- **`167 → 117`: finite term-structural definability is refuted**, by
  `Equation117_not_termStructuralFromFin_Equation167` in
  [Rev167a_c0.lean](../equational_theories/Definability/Rev167a_c0.lean).
  The certificate is on a four-element source: target-realizing clone
  operations are trapped in subclones that cannot recover the source.
  Conditional commentary about division in right quasigroups is not a theorem
  about every E167 magma.

For both `167 → 117` and `332 → 3`, S/all and S/fin remain open while
TS/all and TS/fin are refuted and TD/all is positive. Their current task is
therefore FO recovery, not a missing reversible term.

The previously suggested pairs `467 → 437`, `473 → 429`, `477 → 417`,
`481 → 452`, `504 → 427`, and `879 → 632` still illustrate a different task:
TS and S are positive for finite carriers but open for arbitrary carriers;
TD and D are already positive for arbitrary carriers. An infinite obstruction
or a finiteness-free recovery argument would address the actual missing cells.
This is a useful research direction, not a guarantee that the law forces
bijectivity or that its existing finite construction extends.

## 5. Open in Lean, pending external proof, or mathematically unknown?

The audit does **not** conflate these. The status vocabulary is:

| Evidence state | Meaning here |
|---|---|
| Board proved/refuted | An extracted declaration or closure consequence; validation limits are below. |
| Explicit external proof awaiting formalization | Requires a cited proof/certificate of the **exact** relation and carrier flavour. A solver attempt or conditional parastrophy comment is not enough. |
| Claimed or sketched only | There is a suggestion, but its hypotheses, recovery, or quantifiers have not been justified for this cell. The historical commentary shortlist is evidence for ideas, not blanket proof promises. |
| Unresolved in this checkout | No resolution was found by this source scan and closure. This is the default evidence label for every inventory entry. |
| Known open in mathematics | Requires an explicit mathematical source asserting the precise question remains open. No such label is inferred from absence of a Lean proof. |

No external-proof backlog is being silently credited here. The finite E677
implication has the explicit project reference above; the other inventory
entries are not automatically given the same mathematical-open label. This
audit does not certify a literature-wide “unknown to math” classification.
The old `defwork/` search workspace is absent from
this checkout. Its historical descriptions do not establish which unreplayed
certificates, if any, are currently available. A future pending-proof entry
should record the directed pair, relation/flavour, proof source, exact missing
Lean obligation, and whether the proposal supplies recovery and works on
infinite carriers. Until then it remains **unresolved in this checkout**.

## 6. Validation and reproducibility

This snapshot was collected with working-tree changes to `GaussianRecovery`
and the entry-point import;
the HEAD commit alone does not reproduce it. The JSON records the full HEAD
identifier and a SHA-256 fingerprint of all scanned project Lean files,
`data/duals.json`, `data/equations.txt`, the parser, import reader, and audit generator. It verifies
that those inputs did not change during collection. The fingerprint is also
printed in the generated totals.
The recorded HEAD is historical provenance: `--check` compares source inputs
and results, not whether another commit has since advanced the branch.

Checks performed for this audit:

- `lake build equational_theories.Definability` succeeded: **16,631 jobs,
  139.53 seconds** elapsed with existing build artifacts. This is an incremental
  build, not a cold-build benchmark.
- The source scan rejects board-affecting definability declarations/families
  outside that entry point's import closure.
- All ten optimized negative propagations were compared with the full-matrix
  reference computation. Positive/negative clashes are rejected.
- The hierarchy, all class partitions, every positive/negative class rectangle,
  complete open-cell expansion, and raw totals were checked.
- The regression suite includes random closure comparisons and a test in which
  another relation's status differs inside an audited class rectangle; all
  **15 tests passed**, including commit-stable snapshot verification and
  hypothetical closure impacts checked against full recomputation.
  Full collection, reference comparison, validation,
  and documentation generation took **202.90 seconds** locally.

A successful Lean build alone permits axioms and `sorry`, so it is not a
repository-wide axiom audit. The two RowCycle, six SquareSwap, and 47
ArgumentSwapCatalogue declarations and the three new GaussianRecovery
refutations have explicit `#guard_msgs` axiom checks,
as do all 55 shortened normal-form obligations; that fact must not be
generalized to every seed. See the [square-swap](definability_reversible.md)
and [argument-swap](definability_argument_swap.md) guides for the constructions,
source-law arguments, certificate reuse, and proof organization. The
[Gaussian recovery guide](definability_gaussian_recovery.md) explains the
shared infinite countermodel and the precise scope of its three obstructions.
The report still uses a source-pattern parser, not elaborated theorem
reflection, and does not supply a proof dependency path for every closed cell.
Its report of zero open cells is relative to those extracted inputs.

The [complete diagnostic appendix](definability_open/diagnostics.md) lists
skipped conjectures, unparsed attributed statements, attributed source files
outside the Definability import closure, unpaired certificate families, and
every negative declaration with a carrier-classification warning. In particular,
an explicit `FromFin` statement seeds the finite board even if the parser cannot
find a witness carrier in its proof. Check “finite closure” before treating a
warning as a missing result.

The concrete diagnostic findings are:

- **No unparsed attributed implication statements**, no orphan definability
  declarations, and no positive/negative clashes. The implication scan skips
  **27 conjecture declarations** rather than treating them as proofs.
- **1,172 of 1,221 attributed source files lie outside the Definability import
  closure.** They belong to the original implication development; the
  Definability-only build above is **not** a fresh build check of those files.
  They are listed in full rather than silently covered by a “build passed” claim.
- Of **119 negative declarations with carrier warnings**, the 30 in
  [TransvectionE9](../equational_theories/Definability/TransvectionE9.lean)
  explicitly state `FromFin` refutations: all are already finite seeds and
  finite negatives in closure. The 84 in
  [R1516Cover](../equational_theories/Definability/R1516Cover.lean) use the
  characteristic-zero quotient-ring carrier defined in
  [R1516](../equational_theories/Definability/R1516.lean), and the two in
  [Semilattice](../equational_theories/Definability/Semilattice.lean) use
  nonempty finite subsets of **all integers**—an infinite carrier. The three
  new GaussianRecovery declarations use **all Gaussian integers**, likewise
  an infinite carrier; the parser conservatively leaves `GaussianInt`
  unclassified rather than inferring a finite witness.
  Their all-only classification is appropriate; these warnings reveal no
  omitted finite seed.
- There are **287 paired certificate families**. The only unpaired
  `Satisfies` family is `negInt`, intentionally an infinite **clone**
  obstruction, not a finite FO symmetry rectangle. Its concrete negative
  declarations are in
  [LinearIntCover](../equational_theories/Definability/LinearIntCover.lean)
  and are scanned normally. There are no unpaired `FamilyRefutes` families.

To regenerate or verify the inventory from the repository root:

```sh
lake build equational_theories.Definability
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_audit.py --write --date 2026-09-16 --verify-closure
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_audit.py --check --verify-closure
OPENBLAS_NUM_THREADS=2 python3 scripts/test_definable.py
```

`--check` recomputes from Lean and compares the snapshot and all generated
appendices. `--render` only rerenders Markdown from the saved JSON; it does
**not** refresh or validate the board. The present overview is hand-maintained
mathematical exposition; generated appendices and JSON are the authoritative
enumeration at the recorded snapshot. For a current individual query, use
`scripts/definable.py --query SOURCE TARGET`; for development conventions, see
[the workflow](definability_workflow.md).

To expand an entire board's open inventory without rerunning the source scan:

```python
import json
from pathlib import Path

snapshot = json.loads(Path("docs/definability_open/snapshot.json").read_text())
entry = snapshot["boards"]["structural/all"]
classes = entry["classes"]
for source_rep, profile_groups in entry["open_rows"].items():
    for representative_profile, target_reps in profile_groups.items():
        for target_rep in target_reps:
            for source in classes[source_rep]:
                for target in classes[str(target_rep)]:
                    print(source, target)  # Every raw open pair exactly once.
```

Use the profile keys for research triage at representatives; do not attach
them to the expanded pairs as though all ten statuses were class-invariant.
