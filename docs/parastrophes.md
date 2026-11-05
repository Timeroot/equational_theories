# Quasigroup laws and their parastrophes

The catalogue at `parastrophes/` and the Equation Explorer's property panel track
questions about the **actual left and right division operations**. These are
separate from the eight existential definability relations. An arbitrary
construction of some target magma does not identify its operation with division.
In the other direction, the parastrophe attributes now generate checked structural
arrows and fine-spectrum equalities, which are exported to the relation viewers.

For an operation `*`, left division `x \ y` is the unique solution of `x * z = y`;
right division `x / y` is the unique solution of `z * y = x`. Together with `*`
and the opposites of these three operations, these are the six parastrophes.
Some can coincide. A **left quasigroup** has bijective rows, a **right quasigroup**
has bijective columns, and a quasigroup has both. Either division can be studied
without the other one. Empty carriers
are allowed, consistently with the rest of the project.

## Questions and quantifiers

Every numbered law has separate `all` (possibly infinite) and `fin` fields:

| Field | Lean predicate | Meaning |
|---|---|---|
| Always a left/right quasigroup | `SideQuasigroupLaw scope L side` | Every model has bijective translations on this side; the other side is unrestricted. |
| Always a quasigroup | `QuasigroupLaw scope L` | Every model of L in this scope has bijective rows and columns. |
| Left/right image characterized by one equation | `SingleEquation scope L side` | There is an identity whose complete model class is exactly this division image. |
| Left/right term per model | `TermRecovery scope L side` | For every L-model, there exists a parameter-free binary term for the specified division. |
| Left/right uniform term | `UniformTermRecovery scope L side` | There exists one binary term that works for every L-model in the scope. |

`Characterizes scope L side target` provides a specified witness for
`SingleEquation`. Its definition is an iff over **all target magmas**, so it
includes the converse and excludes extra target models lacking the relevant
one-sided division. `InImage L side D` means that some L-model M has D as its
specified division; it does **not** require M to be a two-sided quasigroup.
`IsDivision` itself supplies bijectivity on that side for both M and D.

The viewer assesses applicability **separately on each side**. A counterexample
to right bijectivity makes only the right division questions not applicable;
left division can remain proved, unknown, or negatively characterized. A negative
`QuasigroupLaw` alone does not determine which side fails and suppresses neither.
If one side is universally bijective and quasigroupness has a counterexample,
that counterexample must fail on the other side. The closure records both premises.
The aggregate two-sided column is retained as a useful summary, alongside the
eight one-sided questions (four on each side) in each scope.

`SingleEquation` quantifies over `Law.NatMagmaLaw`, with arbitrarily many finite
variables and operations. A negative excludes **every single identity**, not
merely the 4694 catalogue equations. Positive records can name an equation outside
the numbered catalogue; its actual syntax is exported and displayed.

For the literature on compressing finite identity bases to one equation, and
the hypotheses that obstruct direct application to E714 and E872, see
[the single-identity research notes](parastrophe-single-identity-literature.md).

Term recovery does not require a positive single-equation characterization.
`IsDivision` asserts both inverse identities. Thus a recovery term denotes the
actual division, not just an arbitrary right inverse or an operation satisfying
some target law. The terms contain no parameters or extra constants.

## Automatic structural and fine-spectrum consequences

`@[parastrophe_result]` now creates kernel-checked consequence theorems in addition
to recording the original question. `Parastrophes/Consequences.lean` proves the
conversions once; the attribute applies them without searching for graph paths.

* `Characterizes scope A side B` always gives the **B → A FO-structural** arrow:
  every B-operation has an A-operation as its division. Division is defined by
  the atomic formula `x * z = y` (left), or `z * y = x` (right), in either direction.
* To obtain a correspondence covering **every A-model**, the registry also needs
  `SideQuasigroupLaw scope A side`, or a registered quasigroup/term theorem that
  supplies it. An exact image alone does not supply this premise for A.
* With that premise, both structural arrows and **the same fine spectrum** are
  registered. `characterizes_modelEquiv` is an actual bijection of models on each
  carrier. `division_preserves_isomorphism` shows that relabelling preserves
  multiplication iff it preserves division. Thus `characterizes_unlabelledEquiv`
  also gives a bijection of isomorphism classes. `SameFineSpectrum.counts` states
  equality of both finite labelled and unlabelled model counts. This is stronger
  than equality of the sets of orders admitting models.
* The same premises already yield **term-structural arrows** in both directions.
  On arbitrary carriers the existing free-model argument supplies the division
  term; on finite carriers inverse translations are powers. Explicit per-model
  or uniform term annotations also trigger registration through their bijectivity
  consequence. No uniform finite term is asserted by this conversion.

The registry revisits exact images when a new annotation arrives, so either
declaration order works. The final `register_parastrophe_consequences` command in
`Parastrophes.lean` combines evidence from separately compiled imports. It checks
side and scope and performs only these type conversions and finite restriction;
it does **not** compute transitive closure or search ordinary implication paths.
Negative records and `@[parastrophe_claim]` never seed positive arrows.

The Lean export includes `consequences` and `consequenceSources`, with generated
theorem names and references to the original evidence and conversion rules.
Both `definable.py` and the website generator consume these native arrows, then
apply their existing relation weakening and transitive closure. The website
builder exports parastrophes **before** building relation boards. The parastrophe
proof panels also show fine-spectrum equality and its Lean evidence. Old exports
without the new fields must be regenerated before computing the relation boards;
they are not silently treated as having no new arrows.

## General results that fill fields automatically

All transfer rules used by the viewer are theorems in `Parastrophes/Basic.lean`
and `Parastrophes/Uniform.lean`, exported with their source locations.

* Positive all-carrier results restrict to finite carriers; finite negatives
  refute the corresponding all-carrier statement. The converses do not hold.
* Uniform term recovery implies term recovery per model, with contraposition.
* On arbitrary carriers, term recovery per model **is equivalent** to uniform
  recovery. Evaluate the former assertion in the free two-generated L-model,
  choose its term, and map the free generators to arbitrary elements of any
  other L-model. Homomorphisms preserve the two inverse identities.
* If L forces bijectivity on one side on arbitrary carriers, **that division
  automatically has a uniform term**. Solve the division equation on the free generators and
  represent the solution by a term. Evaluation homomorphisms transfer the first
  inverse identity; cancellation gives the other one.
* If L forces bijectivity on one side on finite carriers, **that division
  automatically has a term in each model**. On a carrier of size n, every translation's inverse
  is its `(n! - 1)`st iterate. The exponent depends on n, so this does **not** prove
  uniform term recovery across all finite models.
* A recovery term implies bijectivity on its own side. Both sides together imply
  quasigroupness; the proof display includes both premises.
* An exact characterizing target law forces bijectivity on the specified side.
  It forces both sides only when the source law also forces both sides. The
  source quasigroup proof is an explicit additional premise, not an assumption.
* Exact characterization reverses when every source model has that division:
  taking the same division twice recovers the original operation. This uses
  `characterizes_symm`, with the source one-sided property as a premise.
* If the division equals multiplication itself, the exact image is the original
  law. If it equals the opposite operation, the image is the dual law. Neither
  rule needs the other side to be bijective.

Consequently, for each side already known to be bijective, the genuinely
additional term question is **uniform recovery in the finite-only setting**.
The all-carrier and per-finite-model term questions are filled by these general
Lean results even when no convenient short witness has been recorded.

Ordinary implication transfers the universal one-sided, quasigroup and term properties
**backwards for positive results and forwards for counterexamples**: if X implies Y,
every X-model is a Y-model, so a universal property of Y holds for X, while an
X-counterexample is also a Y-counterexample. A universal property of X need not
hold for Y. This includes left/right bijectivity and both term-recovery questions.
Exact single-equation characterization transfers
only under **ordinary implication equivalence** of source laws. The viewer uses
neither term-structural nor FO-definability equivalence for this purpose. Every
such transfer links its implication path in the ordinary graph.

Duality preserves quasigroup status but swaps left and right. More precisely,
left division of the opposite magma is the opposite of right division, so
characterization targets must also be dualized. An explicit term is transformed
by mirroring its operation tree and interchanging its two variables. A negative
transfers by the same involution.

## Composition and domains of definition

Write L, R and O for left division, right division and the opposite operation.
With `x \ y` solving `x * z = y` and `x / y` solving `z * y = x`:

| Transformation | Result | Required property of M |
|---|---|---|
| L(L(M)) | M | Left quasigroup |
| R(R(M)) | M | Right quasigroup |
| L(O(M)) | O(R(M)) | Right quasigroup |
| R(O(M)) | O(L(M)) | Left quasigroup |
| R(L(M)) | O(R(M)) | Quasigroup |
| L(R(M)) | O(L(M)) | Quasigroup |

For example, solving `z \ y = x` is the same as solving `z * x = y`,
so right division of left division is `(x,y) ↦ y / x`.
The mixed steps are not available merely from one-sided bijectivity.
`division_otherSide_iff` proves that the other side exists after a division iff
it existed before. Thus a left-only quasigroup remains left-only under L;
it does not acquire right division by this process.

These identities are proved in `Basic.lean` as `division_symm`,
`division_opposite`, `right_after_left`, `left_after_right`, and
`division_otherSide_iff`, and are exported with source references in the
website's composition explanation.

## Registering results

Import `equational_theories.Parastrophes.Attributes` and the required source
laws/proofs. Add completed theorems with `@[parastrophe_result]`, for example:

```lean
@[parastrophe_result] theorem myLeftQuasigroupResult :
    Parastrophes.SideQuasigroupLaw .fin Law677 .left := ...

@[parastrophe_result] theorem myRightCounterexample :
    ¬ Parastrophes.SideQuasigroupLaw .fin Law670 .right := ...

@[parastrophe_result] theorem myQuasigroupResult :
    Parastrophes.QuasigroupLaw .all Law543 := ...

@[parastrophe_result] theorem myExactCharacterization :
    Parastrophes.Characterizes .all Law14 .left Law29 := ...

@[parastrophe_result] theorem myDivisionTerm :
    Parastrophes.UniformTermWitness .all Law543 .left
      (FreeMagma.Fork (FreeMagma.Leaf 0) (FreeMagma.Leaf 1)) := ...

@[parastrophe_result] theorem noSingleIdentity :
    ¬ Parastrophes.SingleEquation .all Law543 .right := ...
```

The attribute derives equation number, carrier scope, polarity, division side,
target identity and explicit term from the theorem's **type**. The source must be
a named catalogue constant such as `Law543`. It rejects:

* non-theorems or conditional/generalized statements of the wrong shape;
* a refutation of one candidate target or one term presented as a global negative;
* `sorry` and axioms other than `propext`, `Classical.choice`, and `Quot.sound`.

An existential uniform proof can use `UniformTermRecovery` instead of
`UniformTermWitness`; its truth is exported without claiming a specific term.
Prefer a negative `SideQuasigroupLaw` when the counterexample identifies which
translation fails. It implies a negative `QuasigroupLaw`, while a two-sided
negative alone cannot identify either side. The theorem's docstring should
identify the failed translation or collision.

`@[parastrophe_claim]` accepts the same precisely typed questions as conjectural
records, with a required explanatory docstring and an optional `sorry` gap.
They display as conjectural, never as proved and never as premises of proved
closure. No purported proof means **no annotation**: the cell remains unknown.
The initial catalogue has no conjectural placeholders.

Import modules containing annotations into `equational_theories/Parastrophes.lean`.
The exporter reads the persistent attribute extension, so there is no second
hard-coded list of theorems to maintain. The initial records live in
`Parastrophes/Catalogue.lean`.

## Initial examples

* E2: subsingleton magmas, with the same law characterizing each division image.
* E14: both divisions are `y ◇ x`, with exact target E29. Duality also gives E29.
* E543: the operation is abelian-group subtraction. Left division is subtraction
  itself and has exact characterization E543. Right division is addition, with
  the uniform term `x ◇ ((x ◇ x) ◇ y)`. No identity characterizes that image on
  arbitrary carriers: integer addition belongs to it, all its identities hold
  in its natural-number submagma, and natural-number addition is not a quasigroup.
  This obstruction is formalized without a model-search certificate. The separate
  `FiniteGroupImage.lean` argument below now also proves the finite analogue.
* E704, E1279 and E1313: existing finite Latin-square reductions are registered;
  the general finite theorem supplies their terms per model. Their uniform
  finite terms are not asserted by those reductions. The later population pass
  supplies explicit left division terms separately in `FiniteSolutions.lean`.
* E1, E3, E4, E46 and E168: small explicit non-quasigroup countermodels seed
  negatives. The E168 example is the four-element central groupoid
  `(a,b) ◇ (c,d) = (b,c)`.

## Historical population audit (15 October 2026, before the side split)

Before splitting one-sided applicability, the catalogue had **110 checked result declarations** and **20 checked transfer
rules**. The following counts use the former two-sided applicability rule and
are retained only as a historical baseline; they are not current completion
counts. After ordinary implication and duality closure:

| Scope | Quasigroup: yes | Quasigroup: no | Quasigroup: unknown | All applicable fields settled |
|---|---:|---:|---:|---:|
| Arbitrary carriers | 1634 | 3016 | 44 | 4598 / 4694 (98.0%) |
| Finite carriers | 1698 | 2990 | 6 | 4560 / 4694 (97.1%) |

These are counts of numbered laws, before quotienting by implication equivalence
or duality. A proved non-quasigroup law is a completed row: its division-image
questions are not applicable. The unresolved-row counts decreased from 216 to
96 on arbitrary carriers, and from 228 to 134 on finite carriers. Exact
single-equation characterization remains the main gap among quasigroup laws.

The integrations are grouped by proof:

* `Parastrophes/SmallCounterexamples.lean` contains five three-element tables
  (E508, E1489, E1523, E1682, E1685), four-element tables for E501 and E670,
  and a five-element table for E474. The three-element tables were selected
  from an exhaustive sweep of all 2- and 3-element operations: the two-element
  negatives were already covered, and the five new three-element seeds cover
  22 formerly unknown laws by implication and duality. All tables, equations
  and collisions are checked by ordinary kernel reduction.
* `FiniteQuasigroups.lean` wraps the existing cancellation proofs in
  `DivisionCover`, `QuasigroupCover`, `QuasigroupInverse`, `Cancel1516`, and the
  spectrum reductions. Six short factorization arguments additionally record
  that every factor of an identity permutation of a finite set is bijective.
  Existing private lemmas needed here were made public, without duplicating
  their proof bodies.
* `DivisionTerms.lean` records 21 explicit terms using existing equational
  implication proofs for their two inverse identities. `FiniteDivisions.lean`
  adds fixed, size-independent terms for both divisions of finite E63 and E667.
  For E63, right division is two successive left divisions. For E667 it is
  `(x*x) left-divide (x left-divide y)`. `FiniteSolutions.lean` adds 14 more
  fixed left-division terms: the source equation already supplies a right
  inverse to every left translation, and finiteness supplies the converse.
  This works even for E677, E870 and E907 without asserting quasigroupness;
  the unresolved side is right cancellation.
* `Exact.lean` records E546 ↔ E556 by left division on arbitrary carriers,
  E546's right-division self-characterization, and E63 ↔ E125 by left division
  on finite carriers. It reuses the actual transformations from
  `Parastrophic` and `PositiveStructural`, checking that they are the divisions.
  Two generic theorems also handle a division that is multiplication itself or
  multiplication with swapped arguments. With quasigroupness, the exact image
  is respectively the source law or its dual. The viewer applies these rules
  to stronger source laws with their own image law and records both premises.
* `Twists.lean` registers E1719's existing semisymmetric isotope and E880's
  explicit inverse calculation. Both establish quasigroupness without
  finiteness. `InfiniteCounterexamples.lean` wraps the existing infinite
  countermodels for E63, E73, E118, E115, E477, E680, E481, E707, E883,
  E1086, E1113, and E1516. These laws
  have finite quasigroup models universally but need not be quasigroups on
  arbitrary carriers.

The remaining **finite quasigroup gaps** are E677, E870, E907 and their duals
E2910, E2697, E2700. Existing E677 and E907 work supplies left cancellation,
not both sides. Short searches excluding Latin tables found no further models
at orders 4 or 5; order-6 searches timed out. These search outcomes are not
proofs and are not exported as results.

A reversible pair of arbitrary terms, or a parastrophy statement conditional
on already being a quasigroup, is insufficient for an exact characterization.
In particular, the commentary pairs (53,66), (65,1491), (439,510), (464,714),
and (653,960) cannot simply be tagged as unconditional exact correspondences.
The general target question ranges over identities of any length; failure of
one numbered candidate is not a negative answer. Those gaps are retained.

For current counts and the remaining individual equations, run:

```sh
node scripts/parastrophe_inventory.mjs
node scripts/parastrophe_inventory.mjs --json
```

The website now preserves concrete division terms when a generic existence
proof reached the same cell first; the concrete term's own Lean provenance is
retained and propagated to other applicable laws.

## First bijectivity audit (17 October 2026)

This pass added **44 kernel-checked declarations**, bringing the catalogue
to **312 proved records** and 36 general transfer rules. Counts below include
ordinary implication and duality closure over all 4694 numbered equations.

| Unresolved question | Before this pass | After this pass |
|---|---:|---:|
| Arbitrary-carrier quasigroup status | 26 | 18 |
| Arbitrary-carrier left bijectivity | 121 | 43 |
| Arbitrary-carrier right bijectivity | 121 | 43 |
| Finite quasigroup status | 6 | 6 |
| Finite left bijectivity | 4 | 3 |
| Finite right bijectivity | 4 | 3 |

Fully settled rows increase from 4446 to **4518** for arbitrary carriers; the
finite count remains **4464** because the new bijectivity results do not settle
all the independent image-characterization and uniform-term questions.

The main proof families are:

* `TranslationLoops.lean`: if every left translation has a right inverse made
  from other left translations, all these maps are surjective. The inverse word
  is therefore surjective too, forcing the original map to be injective. This
  upgrades E716, E1122 and E1325 to arbitrary carriers, with explicit terms.
* `InverseIdentities.lean`: seven short equational calculations upgrade the
  finite left-division terms for E72, E117, E501, E703, E910, E916 and E1525 to
  arbitrary carriers. Vampire found the steps; Lean replays and checks them.
* `BijectivityCountermodels.lean` and the infinite-counterexample modules:
  bijectivity would force an additional identity violated by a saved model.
  Other proofs identify actual collisions or omitted values in those models.
  In particular, both sides now have negative arbitrary-carrier results for
  E63, E115, E118, E467, E1076, E1110, E1276, E1516, E1692 and E1729.
* `Equation1518.lean`: translations indexed by squares are surjective, and
  `(y*y)*y = y*y`. On a finite carrier they are injective, so equal squares have
  equal roots. Squaring is then a permutation; consequently every left
  translation is bijective. E2054 gets the dual result. **Uniform finite term
  recovery remains open** for these two sides; per-model recovery is proved.
* `MoreInfiniteCounterexamples.lean`: an E677 quasigroup must satisfy E255.
  Right surjectivity gives a fixer of each element, and left cancellation
  identifies it as `(x*x)*x`. The existing infinite countermodel to E255 thus
  settles E677's arbitrary-carrier quasigroup status negatively.

The remaining finite bijectivity questions are precisely **right bijectivity
for E677, E870 and E907**, and left bijectivity for their duals E2910, E2697 and
E2700. These are also exactly the remaining finite quasigroup-status questions.
Up to duality, arbitrary-carrier quasigroup status remains open for E464, E667,
E704, E870, E907, E1083, E1279, E1286 and E1313. The inventory command above lists
the additional one-sided gaps individually.

## Further bijectivity results (17 October 2026)

This continuation adds **22 kernel-checked declarations**, bringing the catalogue
to **334 records**. Duality and ordinary implication are included in these counts:

| Unresolved question | Before this continuation | After |
|---|---:|---:|
| Arbitrary-carrier quasigroup status | 18 | 12 |
| Arbitrary-carrier left bijectivity | 43 | 23 |
| Arbitrary-carrier right bijectivity | 43 | 23 |
| Finite quasigroup status | 6 | 4 |
| Finite left bijectivity | 3 | 2 |
| Finite right bijectivity | 3 | 2 |

Fully settled arbitrary-carrier rows rise from 4518 to **4546**; finite fully
settled rows remain 4464. The 148 generated structural/fine-spectrum consequences
are unchanged: these additions settle division status and terms without adding
new exact-image characterizations.

`Equation870.lean` closes **finite E870 quasigroup status positively**, including
a uniform right-division term. Write `D(a,b)` for left division, already known
in finite models. E870 says

```
D(y,x) = (x*x)*(x*y).
```

For fixed `x`, this column of `D` is the composition `L_(x*x) ∘ L_x` of two
permutations. Left division preserves right-quasigroup status, so multiplication
also has bijective columns. Its right division is explicitly
`x / y = D(x, D(x*x,y))`; the registered witness expands both divisions into
multiplication. This proof uses no computation depending on the order.
E870's right division image still has no single-equation characterization.

`CancellationIdentities.lean` supplies fixed left-division terms for **E690 and
E1353 on arbitrary carriers**. Short cancellation arguments found by Vampire
are replayed as equational steps in Lean; no ATP answer is trusted.

`GreedyCollisions.lean` gives new **arbitrary-carrier negatives**:

* E503 and E677 admit a row collision `0*1 = 0*2 = 3`, using their existing
  countable completion constructions. The saved E677 countermodel also has
  the column collision `1*1 = 2*1 = 2`.
* New completion constructions in `Generated/Greedy/EqN.lean` retain a row
  collision for **E466, E474, E676, E679, E704, E706, E872, E882, E907, E1119,
  E1279 and E1312**.
* The E704, E907 and E1279 constructions retain **both row and column
  collisions**, starting with `0*1 = 0*2 = 2*1 = 3`. This settles their
  arbitrary-carrier quasigroup status negatively. Finite E704 and E1279 models
  are quasigroups; finite E907 quasigroup status remains open.

The E882 and E907 constructions preserve four local rules: functionality, the
partially evaluated source law, and two collision constraints. For E907, fill an undefined
product `a*b` with a fresh `c` and also set `x*c = z` whenever the old table has
`x*z = a` and `z*x = b`. For E882 those two old products are reversed.
Case splits prove preservation directly in Lean. Enumerating all pairs of
natural numbers and taking the increasing union then gives a total operation.
The finite starting tables are checked directly, so these are actual countable
countermodels, without a trusted external solver. The other constructions use
between three and ten local rules. E1119 and E1279 require longer clausal replays
instead of the short case splits used for the other laws. Their Lean sources
are about 409 KB and 230 KB; fresh builds took 218 and 135 seconds respectively
in this run, with other builds running concurrently. There are no external
certificates to download or solvers to run when building these modules.

At this stage the catalogue still listed finite E677 and E907 quasigroup status
as unknown. The E677 entry was a missing import, corrected by the ICARM witnesses
below. Finite E907 right bijectivity remains open.

At that stage, up to duality, the remaining arbitrary-carrier quasigroup questions were **E464,
E667, E870, E1083, E1286 and E1313**. Additional one-sided questions remain; the
inventory command lists all 23 gaps on each side.

Bounded searches for finite right-cancellation counterexamples at orders 6–9
found none; solver timeouts remain unknown. Searches for a unary square-root
term for finite E1518, through four multiplications and assuming left division,
also found no proof. Neither search outcome is exported as a negative theorem.
The completion search was also attempted on the remaining arbitrary-carrier
families. Unfinished candidate rules and the distinction between external
preservation proofs and completed Lean countermodels are saved in
`data/parastrophe_bijectivity_search_20261017.json`.

## ICARM's finite E677 counterexamples (17 October 2026)

`Equation677FiniteCounterexamples.lean` imports two canonical operation tables
from the [ICARM Equation 677 Database](https://eq677.icarm.cloud/), originally
contributed through `memoryleak47/eq677`. We acknowledge ICARM (the NSF Institute
for Computer-Aided Reasoning in Mathematics) and NSF Grant DMS 2425401.
The original tables, source URLs, canonical identifiers and download hashes are
saved in [`data/parastrophes/e677_icarm.json`](../data/parastrophes/e677_icarm.json).
The Lean operations use packed integers for fast kernel lookup.

* [Order 25, `d732efd1`](https://eq677.icarm.cloud/magma/d732efd172ca4d7b9967999fff8c2c19)
  is idempotent and satisfies E677 and E255. Its canonical labeling has
  `1*0 = 10*0 = 14`, so it is not a right quasigroup.
* [Order 49, `fa885ee6`](https://eq677.icarm.cloud/magma/fa885ee6c3df774cdb6f92bab42105d2)
  satisfies E677 and E255 but is not idempotent: `0*0 = 48`. It has the
  right-cancellation failure `18*0 = 19*0 = 18`.

All these assertions are checked in Lean. The two E677 checks have only 625
and 2401 instances respectively; packed lookup lets ordinary kernel reduction
verify them without SAT certificates or native-decide axioms. The module builds
in about 4.2 seconds in this run and its Lean source is under 10 KB. Left
bijectivity for both models follows from the existing general finite E677 theorem.

The registered results `not_rightQuasigroup677_fin` and `not_quasigroup677_fin`
use the smaller witness. Website closure transfers the negatives to the dual
E2910, with left and right exchanged. This corrects a missing import, rather
than resolving a previously open mathematical problem. **Only E907 and its
dual E2700 remain open for finite quasigroup status**; their unresolved sides
are right and left respectively. The catalogue now has **336 records**.

These witnesses do not resolve the finite E677 → E255 problem: both satisfy
E255. For a finite E677 magma, the exact condition equivalent to E255 is that
every column `x` contains the value `x`, i.e. `∀ x, ∃ y, y*x=x`.
`Eq677.eq255_from_fixer_exists` proves sufficiency. Repeated values elsewhere
in a column do not contradict this condition. In particular, trying to prove
that every finite E677 magma is right-bijective cannot settle the implication,
since that stronger assertion is false.

## Infinite idempotent countermodels (17 October 2026)

The next arbitrary-carrier pass constructs idempotent countermodels on `Nat`
for **E1083, E1286 and E1313**, settling those quasigroup and both translation-bijectivity
questions negatively, together with their duals E2504, E2301 and E2294. Their finite
quasigroup theorems remain positive: these are genuine finite/infinite differences.
The new evidence is registered in `Parastrophes/IdempotentInfinite.lean`.

For E1286 and E1313, the construction starts with every diagonal product `x*x=x` and the four
prescribed products `0*1=0*2=1*0=2*0=3`. It then enumerates the pairs of natural
numbers. For each undefined product it chooses a fresh number, adds that product
and its forced companions, and checks that the partial table still satisfies a
short list of closure and uniqueness conditions. Only finitely many off-diagonal
products have been defined at each stage, so fresh numbers remain available.
The increasing union defines a total operation, satisfies the original equation,
and retains both cancellation failures. Unlike the earlier finite-support
completion constructions, the diagonal is present on the entire infinite carrier
from the start. This extra structure makes these completion rules manageable.

`Generated/Greedy/Eq1083Idempotent.lean`, `Eq1286Idempotent.lean` and
`Eq1313Idempotent.lean` contain the extension, completion and seed proofs. Vampire suggested the invariants, but
Lean checks all of them directly; there are no external certificates, `sorry`s,
or native-decision axioms in these proofs. Research inputs and the unfinished
E63/E464 invariant sets are saved in
[`data/parastrophes/arbitrary_idempotent_20261017.json`](../data/parastrophes/arbitrary_idempotent_20261017.json).
E1083 has a sharper distinction between cancellation and bijectivity.
`Parastrophes/Equation1083.lean` proves that every right translation is injective
on arbitrary carriers: the composite `x ↦ y*(x*y)` is a permutation, with inverse
`x ↦ x*(y*x)`. The infinite idempotent seed has `0*1=0*2=3` and `4*0=1`.
Consequently its zero column **misses 2**. If `x*0=2`, the permutation above would
send both x and 4 to 3, forcing `x=4`, contrary to `4*0=1`. Thus the row failure
is noninjectivity, whereas the column failure is nonsurjectivity. This specific
missing-value assertion is also checked in Lean.

At this stage the arbitrary-carrier quasigroup gaps fell from **12 to 6**. Up to duality,
only **E464, E667 and E870** remained in that list. The one-sided bijectivity gaps
fell from **23 to 17 on each side**, and fully settled arbitrary-carrier rows
increased from **4546 to 4552**. The catalogue exported **342 proved records**.
Finite E907 and its dual remain
the two finite quasigroup gaps; this pass does not investigate them.

### E667 and E870: a common free-group countermodel

The follow-up pass settles **E667, E870 and their duals E2900, E2697** negatively
on arbitrary carriers. Both laws reduce to E63 under idempotence. The new
[`ManuallyProved/Equation63Idempotent.lean`](../equational_theories/ManuallyProved/Equation63Idempotent.lean)
constructs an idempotent E63 model on `FreeGroup Nat` with failures of both left
and right cancellation. All four catalogue results are registered in
`Parastrophes/IdempotentInfinite.lean` and propagate to the duals automatically.
Their finite quasigroup results remain positive.

Write the operation as `x ◇ y = x f(x⁻¹ y)`, using group multiplication on the
right. E63 becomes the functional equation `f(x⁻¹ f(f(x))) = x⁻¹`; idempotence
is just `f(1)=1`. Adapt the existing E63 free-group completion, starting with
five prescribed values, where the six generators below are distinct:

```
f(1) = 1
f(g₁) = f(g₂) = g₃
f(g₄⁻¹) = g₄⁻¹ g₆
f(g₅⁻¹) = g₅⁻¹ g₆
```

These force `1 ◇ g₁ = 1 ◇ g₂ = g₃` and `g₄ ◇ 1 = g₅ ◇ 1 = g₆`.
To define an undefined value `f(d)`, choose a fresh free generator `c` and add
the finitely many companion values forced by the functional equation. Projection
onto the exponent of `c`, together with four auxiliary invariants, proves that
the extension remains consistent. A greedy chain supplies a total function
while preserving the seed. The extension argument and the five-pair seed are
kernel-checked; there are no external proof certificates or `sorry`s. The new
construction module built in approximately 13 seconds locally.

After closure there are **346 registered records**, **4556 fully settled
arbitrary-carrier rows**, and **13 bijectivity gaps per side**, down from 17.
Only **E464 and its dual E3103** remain among the arbitrary-carrier quasigroup
gaps, down from six. The finite inventory is unchanged: E907 and E2700 remain
the two quasigroup gaps.

### E464 research checkpoint (superseded on 3 November)

The obstacle described here is now resolved by the invariant-preserving
completion in `ManuallyProved/Equation464Idempotent.lean`; see the final
E464 section below. This paragraph records the earlier experimental stage.

For the same group-based operation, E464 becomes `f(x⁻¹ f³(x)) = x⁻¹`.
An experimental finite partial-function completion survived 2000 extension
steps from the same collision seed, reaching 2844 pairs. This is **not** a
total model or an extension theorem: the scheduling did not exhaust all free
words, and the invariants have not been proved sufficient.

The extra iterate creates a concrete obstacle to copying the E63 proof. If
the old partial function has `f²(h)=d` and `f(h⁻¹)=d`, adjoining `f(d)=c`
forces the path `h⁻¹c → h⁻¹ → d → c`, and hence the additional value
`f(c⁻¹hc)=c⁻¹h`. The new input has zero exponent of `c`, so the simple
exponent projection cannot separate it from old inputs. One must exclude
this configuration by stronger invariants, or handle it using more extension
rules and free-word analysis. The successful finite experiments do not resolve
that issue. Research details are recorded in
[`data/parastrophes/free_group_idempotent_20261017.json`](../data/parastrophes/free_group_idempotent_20261017.json).

## Algebraic division-image obstructions (19 October 2026)

The existing negative image characterizations use an identity-preservation
obstruction. For example, E543's right-division image contains addition on every
finite cyclic group. Any identity holding on all those groups holds on natural
addition (reduce modulo a sufficiently large number), then on Boolean OR via
the map testing whether a natural number is positive. Boolean OR is finite and
has a constant translation, so it cannot belong to the division image. The same
argument works for positive weighted addition. These arguments exclude identities
of every length, not just possible targets in the numbered catalogue.

The new pass replaces integer weights by **algebraic weights represented by
integer matrices**. Two matrices suffice for seven families:

```
Golden:  T(x₀,x₁)    = (x₁,x₀+x₁),       T² = T+I
Plastic: T(x₀,x₁,x₂) = (x₂,x₀+x₂,x₁),    T³ = T+I
```

Both have integer inverses, so their source and division operations reduce
modulo every positive integer. If a putative image identity holds in every
finite reduction, it holds on the integer vectors: a nonzero coordinate
difference survives reduction modulo a sufficiently large modulus. Evaluate T
at its positive real root. In each of the seven families, division becomes
`a*x+b*y` with **both coefficients positive**. A term evaluated on zeros and
ones is zero exactly when the corresponding Boolean-OR term is false. Thus
the putative identity holds on Boolean OR, again contradicting bijectivity.
In fact the same reasoning excludes any collection of identities, though the
catalogue records the single-equation conclusion.

[`AffineImageObstructions.lean`](../equational_theories/Parastrophes/AffineImageObstructions.lean)
proves the common reduction and positivity argument;
[`GoldenImageObstructions.lean`](../equational_theories/Parastrophes/GoldenImageObstructions.lean)
and [`PlasticImageObstructions.lean`](../equational_theories/Parastrophes/PlasticImageObstructions.lean)
check the matrices and their real evaluations. The extra source identities are
checked coordinatewise in
[`MatrixImageCatalogue.lean`](../equational_theories/Parastrophes/MatrixImageCatalogue.lean).
All proofs are in Lean, with no `sorry`s or external proof certificates.

The **19 new registered results** close **28 finite image cells per side** after
ordinary equivalence and duality, reducing the unknown count from **146 to 118**.
For arbitrary carriers, **five applicable cells per side** close, reducing
**82 to 77**; other negatives concern sides already marked not applicable there.
Fully settled rows increase **4556 → 4558** on arbitrary carriers and
**4464 → 4492** on finite carriers. The catalogue exports **365 records**.
Quasigroup and bijectivity status is unchanged.

Notable new finite negatives include **E63's right division, both divisions of
E667, E467's right division, and E125's right division**. The positive finite
left-image characterizations of E63 and E125 remain valid. Term recovery is an
independent question: E125's right division still has a proved uniform term.

Exact coefficient checks can be reproduced with
`python3 scripts/parastrophe_matrix_image_scan.py`. Family details and further,
unformalized algebraic candidates are saved in
[`data/parastrophes/affine_image_obstructions_20261019.json`](../data/parastrophes/affine_image_obstructions_20261019.json).
The latter are research leads, not exported results.

## More algebraic image obstructions (20 October 2026)

[`HigherDegreeImageObstructions.lean`](../equational_theories/Parastrophes/HigherDegreeImageObstructions.lean)
extends the previous construction to nine families of integer matrices of
dimension three to five. Write the source operation as `a(T)x + b(T)y`, where
T is a companion matrix. Its left division is `p(T)x + q(T)y`, with the integer
polynomial identities `bq = 1` and `a + bp = 0` modulo the companion polynomial.
Thus all operations reduce modulo **every** positive integer, including composite
moduli. The source laws and inverse identities are proved by symbolic coordinate
calculations over an arbitrary commutative ring.

| New finite left-image negatives | Companion polynomial f(t) | Source a(t), b(t) |
|---|---|---|
| E670 | t⁴ − 2t³ + t − 1 | 1−t, t |
| E676, E1285 | t³ − t² − 1 | 1−t, t |
| E870 | t³ − t² − 1 | −1−t², t |
| E1083 | t³ − t² − 1 | −t, t²−t |
| E713 | t³ − t² − t − 1 | 1−t, t |
| E1288 | t³ − 2t² − 1 | 1−t, t |
| E1076, E2294 | t⁴ − t³ − t² + t − 1 | 1−t, t |
| E1313, E2531 | t⁴ − 3t³ + 2t² − 1 | 1−t, t |
| E704 | t⁵ − t³ − 2t² − 2t − 1 | t⁴−t³−t²−t−1, t |

The intermediate value theorem supplies a real root t > 1 for each polynomial.
At that root, a(t) < 0 and b(t) > 0, so division has the positive real weights
`−a(t)/b(t)` and `1/b(t)`. The E704 sign check uses
`(t+1)a(t) = −t³`. The shared reduction-to-integers and Boolean-join argument
then rules out **every** single-equation characterization, already on finite
carriers. All twelve new annotations are proved in Lean without `sorry` or
external certificates. The complete module takes about a minute to build in
the current workspace; it does not enumerate the finite models.

After duality and ordinary equivalence, this closes **24 finite image cells**
(12 on each side): the remaining unknown count drops **118 → 106 per side**.
It also closes **six applicable arbitrary-carrier image cells**, dropping
**77 → 74 per side**. Fully settled finite rows increase **4492 → 4510**;
the arbitrary-carrier total stays at 4558 because the affected rows still have
bijectivity gaps. There are now **377 registered records**. Quasigroup,
bijectivity and term-recovery statuses are unchanged.

The coefficient data, inverse polynomials, real-root intervals and theorem names
are in
[`companion_image_obstructions_20261020.json`](../data/parastrophes/companion_image_obstructions_20261020.json).
The command recorded there scans all 4694 equations using exact integer polynomial
arithmetic and also checks the recorded division coefficients. This is a
reproducible discovery tool; the Lean proofs independently check the identities.

This pass also audits implication propagation. The viewer already transfers
universal properties to stronger laws and counterexamples to weaker laws, with
the appropriate Lean transfer lemma and implication path in the proof panel.
Regression tests now explicitly check both directions and reject transfers in
the opposite direction. Bare image-characterization results still require
ordinary equivalence. Our stronger Boolean-join obstruction can be reused for a
weaker source law by proving that the same matrix family satisfies it; the scan
checks for these opportunities, including E1285, E2294 and E2531 above.

## Remaining arbitrary-carrier bijectivity gaps (20 October 2026)

[`RemainingInfinite.lean`](../equational_theories/Parastrophes/RemainingInfinite.lean)
adds six proved left-bijectivity negatives: **E670, E1082, E1085, E1288,
E1315 and E1322**. Duality supplies six right-bijectivity negatives. The finite
left-bijectivity results for all six remain positive: the distinction is an
infinite one. After closure, the inventory reads:

| Measure | Before | After |
|---|---:|---:|
| Arbitrary-carrier bijectivity gaps, per side | 13 | **7** |
| Fully settled arbitrary-carrier rows | 4558 | **4570** |
| Registered results | 377 | **383** |
| Arbitrary-carrier quasigroup gaps | 2 | 2 |
| Finite bijectivity gaps, per side | 1 | 1 |

The remaining **left** gaps are E464, E669, E879, E1075, E1278, E1285 and
E3103. The remaining **right** gaps are E464, E2244, E2254, E2457, E2650,
E2863 and E3103. The two-sided quasigroup gaps are still E464 and E3103.
The finite mystery remains E907 on the right and its dual E2700 on the left.

Five constructions begin with all diagonal products and `0*1=0*2=3`.
They complete a partial operation on natural numbers by successively filling
missing products, using a fresh element and finitely many forced companions.
A finite list of local invariants proves that no step changes an old product;
therefore the completed operation still has the row collision. E1322 uses
an idempotent E124 construction, since those two laws agree under idempotence.
E1315 needs six partial-operation invariants. Its first-order extension proof is
replayed as separate Lean lemmas to avoid a single large elaboration context.
The E1315 module built in about 17 seconds locally; the other new completion
modules built in roughly 4–20 seconds. No external solver certificate is trusted.

E1085 is simpler. Its rewrite `y*((x*(y*y))*x) -> x` has no proper
nonvariable self-overlap. Free normal forms consequently satisfy the law.
For two generators a,b, the distinct elements b and
`((a*b)*(a*a))*(a*b)` have the same product on the left with a. The small
normal-form calculation is checked directly in Lean.

There is also a useful restriction on further searches.
[`SeparableOperations.lean`](../equational_theories/Parastrophes/SeparableOperations.lean)
proves that **E464, E669, E879, E1075, E1278 and E1285 always have bijective
rows if their operation is `a(x) · b(y)` over a cancellative multiplication**.
The functions a and b can be arbitrary; they need not preserve multiplication,
and the underlying multiplication need not be associative. A row collision
first gives `b(x)=b(y)`. Comparing the law at `(x,x)` and `(x,y)` and cancelling
on the right gives `a(x)=a(y)`. The diagonal instances then give `x=y`.
Surjectivity follows directly from each law. In particular, affine operations
and separated operations built from noncommutative groups cannot supply these
counterexamples. This conditional result does not settle the unrestricted rows.

Bounded searches also explored unrestricted cancellation proofs and stronger
partial-operation invariants (idempotence, absence of small translation cycles,
and right cancellation). They did not close another gap. Vampire proves left
cancellation for commutative E464 and E879 models; those conditional ATP results
are recorded as research, not exported as Lean theorems. The construction
invariants, seed descriptions, theorem references and search outcomes are saved
in [`remaining_bijectivity_20261020.json`](../data/parastrophes/remaining_bijectivity_20261020.json).

### Follow-up: restrictions on the seven remaining gaps

The next pass does **not** close another unconditional catalogue cell: there
are still seven arbitrary-carrier bijectivity gaps per side and 383 registered
results. It establishes several further restrictions in Lean.

[`Equation464.lean`](../equational_theories/Parastrophes/Equation464.lean)
proves that **every E464 model has surjective translations on both sides**, and
that its left translations are injective exactly when its right translations
are injective. Write `L_a(x)=a*x` and `D_a(x)=x*(x*(x*a))`. The law says
`L_a D_a = id`. Applying D three times gives a right-translation section:
`D_x(D_x(D_x(a)))*a=x`. A left collision propagates through three applications
of L; the original law then turns it into a right collision, and conversely.
Consequently the E464/E3103 side questions are linked: up to duality, the
remaining cells represent **six questions**, rather than seven independently
settleable ones. This link is not a proof that either side is bijective.

**Conditional term recovery (made explicit on 27 October):** define
`d(x,y)=y*(y*(y*x))`. On every E464 model that is a quasigroup,
`x\y=d(x,y)` and `x/y=d(x,d(x,d(x,y)))`. These are fixed multiplication
terms, independent of the carrier or its size. The section identities above
supply one inverse identity on each side, and cancellation supplies the other.
`Equation464.divisions_of_leftQuasigroup` checks both divisions in Lean;
even the assumption of left bijectivity alone suffices. Thus the term questions
have no additional obstruction once the bijectivity question is answered
positively. The unconditional catalogue cells remain open because they also
assert that every E464 model has the division in question.

The same module proves that **commutative E464 has `L_x^6=id`**, so every
translation is bijective even on infinite carriers. The proof replays a short
sequence of equational substitutions in Lean. Commutative E669, E1075 and
E1285 each reduce to E464, so they too cannot provide a counterexample.
The earlier commutative E879 result remains ATP-only.

[`KernelRigidity.lean`](../equational_theories/Parastrophes/KernelRigidity.lean)
strengthens the separated-operation obstruction. For E464, E669, E879, E1075,
E1278 and E1285, **if all rows identify the same pairs of inputs, then every row
is injective**. Indeed, a collision between b and c then makes their entire
columns equal. The law's explicit section transfers this to equality of their
rows; comparing the two diagonal instances gives b=c. Any infinite
counterexample must therefore have collision relations that vary between rows.
These conditional results receive no unconditional catalogue annotation.

Finally, the existing idempotent E124 completion can preserve **right
cancellation** while retaining `0*1=0*2=3`. This is now proved by
`Eq124Idempotent.collisionModel_rightInjective`: the extension lemma preserves
column injectivity at every stage, and hence in the completed operation. It
provides a stronger source model for future term-construction searches.

Bounded searches found no further counterexample. Two reusable research probes
are saved: `scripts/parastrophe_greedy_term_scan.py` tests collision-preserving
operations `t(x,x*y)` in four proved countable constructions;
`scripts/parastrophe_operator_bundles.py` searches operations on a finite base
times an infinite vector space, with coefficients built from binary-tree shift
operators. The latter checked all 40 three-element base models of the six laws,
up to relabeling, within its specified coefficient template. Its positive
control recovers a symbolically checked E1117 collision model. Neither an
unsuccessful search nor a surviving candidate is treated as a Lean result.
The bounds, results and theorem references are recorded in
[`remaining_bijectivity_followup_20261020.json`](../data/parastrophes/remaining_bijectivity_followup_20261020.json).

### Two explicit counterexamples: E669 and E1285

[`FoldedExtensions.lean`](../equational_theories/Parastrophes/FoldedExtensions.lean)
closes **E669 and E1285 negatively for arbitrary-carrier left bijectivity**.
Duality closes E2863 and E2244 on the right. Both counterexamples are
idempotent, and all their ordinary rows are bijective; a single added row has
collisions. There are no search certificates or unfinished proof obligations.

For **E669**, use the integers together with an extra element ∞. On integers
put `x*y=2*x-y`, make ∞ a right zero (`x*∞=∞`), and define

```
∞*n = f(n),    f(n) = if n > 0 then n-1 else n+1.
```

The only new nontrivial instance of E669 reduces to
`f(2*n-f(n))=n`. If n is positive, the inner argument is n+1; otherwise it is
n-1. The outer application returns n in either case. But `f(1)=f(-1)=0`,
so the ∞ row is not injective. This is a concrete countable model.

For **E1285**, choose a positive real β with `β*(1+β)^2=1`. On the reals put
`x*y=-β*x+(1+β)*y`, adjoin the same right zero, and set

```
∞*x = f(x),    f(x) = if x > 0 then x/β-1 else x/β+1.
```

The ordinary instances of the law are polynomial identities using the equation
for β. The new instance is `f(-β*f(x)+(1+β)*x)=x`: its inner argument simplifies
to `β*(x+1)` on the positive half-line and `β*(x-1)` otherwise, so it stays in
the same branch. Again there is a collision, `f(β)=f(-β)=0`. Lean obtains β
by the intermediate value theorem and checks the remaining calculations with
integer or real arithmetic. The complete module builds in about four seconds
in the current workspace.

The construction also explains where this method stops. For E1075 and E1278,
such a right-zero extension would force `f(f(x))=x`, ruling out a collision
in its new row. For E879 it would force `f(f(x*x))=x`; E464 cannot admit this
extension at all when the old carrier is nonempty. These necessary conditions
are also formalized in the same module.

| Measure | Before | After |
|---|---:|---:|
| Arbitrary-carrier bijectivity gaps, per side | 7 | **5** |
| Fully settled arbitrary-carrier rows | 4570 | **4574** |
| Registered results | 383 | **385** |
| Arbitrary-carrier quasigroup gaps | 2 | 2 |
| Finite bijectivity gaps, per side | 1 | 1 |

The remaining left gaps are **E464, E879, E1075, E1278 and E3103**; the right
gaps are **E464, E2254, E2457, E2650 and E3103**. The E464 side equivalence and
duality reduce these to four independent questions. The finite questions remain
E907 on the right and E2700 on the left. The new negatives are registered in the
catalogue and propagated by the existing implication and duality closure.
The construction formulas and bounded follow-up searches are recorded in
[`folded_extensions_20261020.json`](../data/parastrophes/folded_extensions_20261020.json).

### A Gaussian-integer counterexample: E879

[`GaussianFold.lean`](../equational_theories/Parastrophes/GaussianFold.lean)
closes **E879 negatively for arbitrary-carrier left bijectivity**, and hence
E2650 on the right by duality. The model is countable and its proof uses only
small integer calculations, with no external certificate or unfinished proof.

Start with `Bool × ℤ[i]`, with operation
`(b,x)*(c,y)=(c,-x+i*y)`. This satisfies E879, and its square map on the
Gaussian coordinate is `S(x)=(i-1)*x`. Multiplication by `i-1` is injective
but not surjective. Give it a rounded left inverse:

```
g(a,b) = ((b-a) / 2, -((a+b) / 2))       -- integer division
f(false,x) = (true,g(x))
f(true,x)  = (false,x)
```

The Boolean coordinate ensures that `f(f(b,S(x)))=(b,x)`, since `g(S(x))=x`.
Now adjoin ∞, put `x*∞=∞`, and let `∞*x=f(x)`. The only new nontrivial
instance of E879 is exactly that identity. Yet `g(0)=g(i)=0`, so the ∞ row
identifies two distinct inputs. The module checks in about three seconds.

| Measure | Before | After |
|---|---:|---:|
| Arbitrary-carrier bijectivity gaps, per side | 5 | **4** |
| Fully settled arbitrary-carrier rows | 4574 | **4576** |
| Registered results | 385 | **386** |

The remaining left gaps are **E464, E1075, E1278 and E3103**; the right gaps
are **E464, E2254, E2457 and E3103**. E464 has equivalent left and right
questions, and E3103 is its dual, leaving **three independent questions up to
duality**. Finite gaps are unchanged: E907 right and E2700 left.

There is also a stronger Lean-proved limit on extending a model of E1075 or
E1278. Partition the carrier into an old part G and a finite new part I, and
require each product to stay in the part of its right argument. Then **each
new row restricted to G is bijective**, even when G is infinite. Thus no
extension of this form can introduce a collision between old elements in a
new row. This does not rule out constructions with infinitely many new
elements, or products that cross the partition differently.

The proof in
[`FiniteBlockExtensions.lean`](../equational_theories/Parastrophes/FiniteBlockExtensions.lean)
reduces both laws to a general lemma in
[`FiniteInverseFamily.lean`](../equational_theories/Parastrophes/FiniteInverseFamily.lean):
if a finite family of functions satisfies `f_i(f_(p_x(i))(x))=x`, with `p_x`
a permutation of the family for each x, all its functions are bijective.
Surjectivity is immediate. For injectivity, label the chosen preimages of x
by their return functions; these labels are distinct, so finiteness forces
every possible preimage to have one of those labels and coincide with the
chosen preimage. This explains why the attempted finite-block constructions
for the two laws could not work; it does not settle their unrestricted status.

The construction, remaining gaps and bounded unsuccessful searches are recorded
in [`gaussian_fold_20261020.json`](../data/parastrophes/gaussian_fold_20261020.json).

### E1278: completing a collision while keeping squaring injective

[`Equation1278.lean`](../equational_theories/Parastrophes/Equation1278.lean)
starts with just `0*1 = 0*2 = 3`. The greedy construction in
[`Eq1278.lean`](../equational_theories/Generated/Greedy/Eq1278.lean)
extends this partial table to a total E1278 magma on the natural numbers,
retaining both products and the distinction between 1 and 2. Thus E1278
does not force left bijectivity on arbitrary carriers; duality transfers the
failure to right bijectivity for E2254. Finite left bijectivity for E1278
remains proved, so this counterexample is necessarily infinite.

The useful extra invariant is **injectivity of squaring**. Write `S(x)=x*x`
where that product is defined. Four core conditions suffice:
functionality of the partial table, its partial E1278 identity, injectivity
of S, and the following compatibility condition:

```
z*x = z*y  and  S(z)*S(x) = S(z)*S(y)  imply  x = y,
```

whenever all products displayed are defined. The two-product seed satisfies
these conditions: it has no squares yet. A missing product `a*b` can be
assigned a fresh value c, followed by six patterns of forced products, while
preserving all four conditions. Enumerating pairs of natural numbers and
taking this increasing sequence of partial tables gives a total operation.
Thirteen invariants were initially discovered; nine proved redundant, so
their large preservation replays were replaced by short Lean derivations.
Vampire helped discover the extension proof, and Lean replays its individual
first-order and propositional steps. No external certificate checker is
trusted, and no prover is run during the Lean build.

Two further checked observations constrain future work on E1075 and E1278.
[`TranslationPeriods.lean`](../equational_theories/Parastrophes/TranslationPeriods.lean)
gives integer models whose zero row is translation by 1, so there is no
universal finite-period identity for left translations. For E1278 use
`x*y = y + ε(x)`, with ε alternating between +1 and −1 on even and odd x;
for E1075, ε has the repeating pattern `+1,+1,−1,−1`. These particular
models have bijective rows and do not themselves close any status gap.
[`Equation1075.lean`](../equational_theories/Parastrophes/Equation1075.lean)
also proves that a row collision produces a column collision: if `a*b=a*c`,
put `t=(a*(a*b))*a`; then `b*t=c*t=a`. Consequently every right-cancellative
E1075 model has bijective left translations, even on an infinite carrier.

After export and the website's proof closure, arbitrary-carrier bijectivity
gaps fall from **4 to 3 per side**, and fully settled rows rise from
**4576 to 4578**. The remaining left gaps are E464, E1075 and E3103;
the right gaps are E464, E2457 and E3103. Up to duality and the proved
left/right equivalence for E464, these are **two independent questions**.
The finite gaps remain E2700 on the left and E907 on the right.
The construction and research checkpoints are recorded in
[`square_injective_completion_20261021.json`](../data/parastrophes/square_injective_completion_20261021.json).

### E1075: a countable idempotent counterexample

The arbitrary-carrier left-bijectivity question for **E1075 is now negative**.
[`Equation1075Idempotent.lean`](../equational_theories/ManuallyProved/Equation1075Idempotent.lean)
constructs an idempotent E1075 magma on the countable free group with a
noninjective left translation. The registered theorem is
`Parastrophes.Catalogue.not_leftQuasigroup1075_all_collision` in
[`Equation1075.lean`](../equational_theories/Parastrophes/Equation1075.lean).
Duality also settles arbitrary-carrier right bijectivity for **E2457**
negatively. Finite left bijectivity for E1075 remains positive, so the
finite/infinite distinction is essential.

Write the free-group operation by juxtaposition, and define the magma by
`x ◇ y = x f(x⁻¹y)`. E1075 then reduces to the unary identity

```
f(x⁻¹ f(f(x)) f(f(f(x))⁻¹)) = x⁻¹.
```

Start with `f(1)=1` and `f(g₁)=f(g₂)=g₃`, where the three generators are
distinct. The first equality gives idempotence; the other two give a
collision in the row of 1. To define a missing `f(d)`, assign it a fresh
generator c. If `f(f(h))=d⁻¹`, the identity forces
`f(h⁻¹d⁻¹c)=h⁻¹`. When also
`q(h)=h f(h⁻¹) f(f(h⁻¹)⁻¹)` is defined, it forces
`f(c⁻¹d q(h))=c⁻¹d h`. These are all the required new-value patterns.
The fresh generator has exponent sum 1, and every old element has exponent
sum 0. Their degrees distinguish most potential conflicts; a finite list
of auxiliary invariants handles the remaining ones. Lean verifies that
every invariant survives the extension. Scheduling all elements and taking
the increasing union then gives a total function preserving the seed.

The proof is a short, symbolic free-group construction, rather than a
large generated preservation replay. Only the three-entry seed is checked
by `decide`; the construction uses neither `native_decide` nor an external
certificate checker. The earlier unsuccessful partial-table searches are
still recorded as incomplete searches, but no longer indicate an open
E1075 status.

This leaves **E464 and its dual E3103** as the only arbitrary-carrier
left- or right-bijectivity gaps. Their left/right questions are already
proved equivalent, so there is **one independent remaining question**.
The refreshed catalogue has **388 records**, and **4580 of 4694**
arbitrary-carrier rows are fully settled, up from 4578.
The finite gaps remain E2700 on the left and E907 on the right.
The research record is
[`e1075_free_group_completion_20261021.json`](../data/parastrophes/e1075_free_group_completion_20261021.json).

## Exact division images: another pass (22 October 2026)

Nineteen new Lean-proved characterizations reduce the applicable unknown
image cells from **68 to 34 per side on arbitrary carriers**, and from
**106 to 71 per side on finite carriers**. There are no new conjectural
records. The quasigroup and bijectivity gaps are unchanged.

| Scope | Source laws | Exact left-division image |
|---|---|---|
| Arbitrary carriers | E72, E117, E501, E690, E723, E731, E765, E778, E916, E947, E960, E978, E1152, E1184, E1353, E2115 | The source law itself |
| Finite carriers | E669, E1075 | The source law itself |
| Arbitrary carriers | E727 | `x = y * ((z*y) * ((z*y) * x))` |

The arbitrary-carrier statements also apply to finite models. E501 upgrades
an existing finite characterization; ordinary equivalence and duality fill
the other numbered laws and the right-division fields automatically.
For E669 and E1075 the transfer of the identity itself needs no finiteness,
but the **converse characterization** uses finiteness to ensure that every
target model has bijective rows. Their known infinite counterexamples
prevent promoting these self-characterizations to arbitrary carriers.

[`TranslationImages.lean`](../equational_theories/Parastrophes/TranslationImages.lean)
gives direct proofs for E765, E778 and E1184 by reversing compositions of
left translations. For example, E778 says `L_y L_z L_(z*y) = id`.
Put `w = z \ y`; the old relation at `(w,z)` is
`L_w L_z L_y = id`. Inverting it gives
`L_y⁻¹ L_z⁻¹ L_w⁻¹ = id`, exactly E778 for left division.
The converse repeats the same argument, since taking left division twice
recovers the original operation. In each case the target law itself
forces left bijectivity.

[`SelfImages.lean`](../equational_theories/Parastrophes/SelfImages.lean)
proves the other self-images by short equational derivations using the
source identity and both inverse identities. Vampire found these
derivations; Lean checks each substitution, and independently supplies the
target's bijectivity. No external solver or certificate checker runs during
the build. The three new modules total about 43 KB and each built in under
nine seconds in this workspace.

E727 illustrates why the question must include identities **outside the
main four-operation catalogue**. Its exact image has five operation symbols
and is **E10577** in [`eq_size5.txt`](../data/eq_size5.txt). The proof in
[`LongImages.lean`](../equational_theories/Parastrophes/LongImages.lean)
starts from `L_y² L_(z*y) = id`. Substitute `w = z \ y` and invert
`L_w² L_y = id`, obtaining `L_y⁻¹ (L_w⁻¹)² = id`.
This is the displayed five-operation identity for division. Repeating the
calculation proves the converse, and the new identity forces bijectivity
by the same translation-loop argument. The exporter stores its explicit
term tree and Lean theorem; the viewer already supports unnumbered targets.

After closure, **4648 of 4694 arbitrary-carrier rows** and **4580 finite
rows** are fully settled, up from 4580 and 4510 respectively. The export
contains **407 result declarations**, **36 transfer rules**, and **247
generated consequences**. The remaining independent bijectivity questions
are still E464 on arbitrary carriers and E907 on finite carriers, together
with their duals.

The bounded follow-up on E66 found several longer identities satisfied by
its left-division image, but no complete converse. Those searches do not
change its characterization status. The full list of new theorems and the
before/after counts are recorded in
[`exact_images_20261022.json`](../data/parastrophes/exact_images_20261022.json).

## Longer division-image identities (23 October 2026)

The next pass adds four exact characterizations, all checked in Lean:

| Source | Scope | Exact left-division image |
|---|---|---|
| E464 | Arbitrary carriers | E714 |
| E677 | Finite carriers | E9321: `x = y * ((x*y) * (x * (x*y)))` |
| E706 | Arbitrary carriers | E10200: `x = y * ((x*y) * ((x*y) * x))` |
| E66 | Arbitrary carriers | `x = y * (z * ((x * (y * (y * (y * (y * (y*y)))))) * z))` |

E9321 and E10200 use the extended five-operation numbering. E66's target
has nine operation symbols. The explicit term trees and proof declarations
are exported using the existing support for targets outside the main catalogue.

[`RotatedImages.lean`](../equational_theories/Parastrophes/RotatedImages.lean)
proves the first three correspondences by substituting variables and cancelling
three successive divisions. E9321 makes every row surjective; finiteness
then supplies injectivity. E10200 supplies both properties without finiteness.
For E464, the statement characterizes the images of models **that admit left
division**. It does not settle whether every infinite E464 model has that
division. The automatic consequences continue to require the separate source
bijectivity hypothesis before asserting a model-class bijection.

For E66, write `s(x) = x * (x*x)` and `c(y) = L_y^5(y)`. The new identity
is `x = y * (z * ((x * c(y)) * z))`. The proof in
[`Equation66Image.lean`](../equational_theories/Parastrophes/Equation66Image.lean)
first shows, for **any** unary function `c`, that this mixed translation loop
forces bijective rows and a common map `s(x) = z * (x*z)` independent of `z`.
For the specified fifth power, an instance of the loop yields
`x*s(x) = s(s(x))`. Two cancellations then give `x*s(x) = x`, hence E53,
`x = x * (y * (x*y))`. Conversely, E53 with bijective rows makes the common
map an involutive automorphism; five row iterations reduce to two and give
the nine-operation identity. Finally, reversing the multiplication constraints
identifies E53 with E66 under actual left division. All these steps work on
infinite carriers as well as finite ones.

This search also exposed a useful pitfall. Replacing `c(y)` by
`(y*(y*y))*y` gives a seven-operation consequence that passes the affine tests,
but has extra non-affine models. A seven-element quasigroup found during this
pass satisfies that candidate and violates E53; its common map `s` is a
seven-cycle. The table and independently checked failed-converse witness are
saved in the research record. It is not used as Lean evidence or a catalogue
claim. Longer identities were accepted only after proving their converses.

After ordinary-equivalence and duality closure, unknown image cells fall
from **34 to 29 per side on arbitrary carriers**, and from **71 to 65 per
side on finite carriers**. Fully settled rows increase from 4648 to **4652**
and from 4580 to **4588**, respectively. The independent bijectivity gaps
remain E464 on arbitrary carriers and E907 on finite carriers, with their
duals. The export now contains **411 results**, **36 transfer rules**, and
**253 generated consequences**. The two new proof modules total about 12 KB
and build in roughly four seconds each; no external solver runs in the build.

Counts and the search record are in
[`exact_images_20261023.json`](../data/parastrophes/exact_images_20261023.json).

## Common translation squares and square-root reparameterization (23 October 2026)

Two further exact characterizations are now checked in Lean:

* **E703, arbitrary carriers:** the left-division image is **E26546951**,
  the eight-operation identity `x = y * (y * (p(x) * x))`, where
  `p(x) = x * (x * (x * (x * (x*x))))`.
* **E1518, finite carriers:** the left-division image is **E1518 itself**.
  Duality gives the corresponding right-image statements.

[`Equation703Image.lean`](../equational_theories/Parastrophes/Equation703Image.lean)
uses a common inverse of squared translations. For E703 this is
`c(x) = (x*x)*x`; for its image it is `c(x) = p(x)*x`.
In each case `L_y² c = id`, and short equational calculations give `c³ = id`.
Consequently `L_y² = c²` and `L_y⁶ = id`, proving bijectivity even on infinite
carriers. Five applications of a division row therefore recover one original
multiplication. Also, the square of every division row equals c. Reindexing
that common square gives the two semantic transfers. Naming c keeps the two
equational calculations small; the remaining proof is direct cancellation.

The same module checks a nine-element E703 model whose left division fails
E703 at `x = y = 0`. Thus replacing the longer target with E703 itself would
be incorrect, even on finite carriers. This refutes that particular candidate,
not the existence of a single defining equation. The table and both division
identities are checked by ordinary Lean `decide`; there is no external solver
certificate and no `native_decide`.

[`SquareImages.lean`](../equational_theories/Parastrophes/SquareImages.lean)
first proves finite E1518 squaring is bijective, using the previously proved
left bijectivity and `(y*y)*y = y*y`. Choose `r*r = y`. Writing D for left
division, E1518 gives `D(y,x) = x*(r*x)` and `D(y,y) = r`.
Then `D(D(y,y), D(x,D(y,x))) = D(r,r*x) = x`, exactly E1518 for D.
Repeating the transfer proves the converse. Choosing r here does **not**
provide a uniform multiplication term for r: E1518's finite uniform-term
question remains open.

The two modules total about **9.5 KB** and built in **6.6 and 4.9 seconds**
respectively. No new axioms or sorries are used. After implication-equivalence
and duality propagation, unknown image cells fall **29 → 28 per side** on
arbitrary carriers and **65 → 63 per side** on finite carriers. Fully settled
rows rise **4652 → 4654** and **4588 → 4590** respectively. The local export has
**416 records**, **36 transfer rules**, and **256 generated consequences**
(including **79 fine-spectrum records**). These consequence counts include
self-arrows; they are not counts of newly resolved arrows in the main graph.

A six-parastrophe composition audit found no further applicable image gaps
that follow just by composing already recorded characterizations. Other
bounded searches did not resolve their targets; failed candidates and search
limits are recorded in
[`square_images_20261023.json`](../data/parastrophes/square_images_20261023.json).

## Joining inverse identities: E125 on arbitrary carriers (23 October 2026)

E125's left-division image now has a single defining identity even on infinite
carriers. In the canonical extended numbering it is **E353668451589**:

```
u = (z*x)*((z*x)*z)
x = y*(u*(u*y)).
```

Here u is just an abbreviation; the expanded identity has eleven operations.
[`Equation125Image.lean`](../equational_theories/Parastrophes/Equation125Image.lean)
proves that this is exactly **E63 together with E1692**, or equivalently
**E63 plus bijective left translations**. Write `f_y(x)=y*x` and
`g_y(x)=x*(x*y)`. E63 says `f_y g_y = id`, and E1692 says `g_y f_y = id`.
The new identity combines these as `f_y g_y g_z f_z = id`, with independent
parameters y and z. Six equational substitutions recover E63. The outer row
gives surjectivity directly; a collision in the row indexed by z makes the
two copies of u coincide and hence forces the original inputs equal.

For an E125 operation, its left division is `D(x,y)=(x*y)*x`. Conversely, the
original operation is `D(y,D(y,x))`. Short cancellation arguments prove both
semantic transfers. Thus the long identity defines exactly E125's division
image and gives a uniform term in each direction. The same module proves
`sameFineSpectrum125_leftImage`: there are bijections of both labelled and
unlabelled models, on infinite carriers as well as finite ones. Finite E63
already forces injectivity, so the previous finite E125/E63 characterization
remains the shorter description. Infinite E63 has additional models and is
not replaced by the new identity.

The separately tagged `left_characterizes63_all_partial` also records that
**among E63 models admitting left division**, the image is exactly E125 on
arbitrary carriers. It does not supply division to every infinite E63 model.
The new module builds in about **4.7 seconds**, with no sorries, external
certificates, or native checking. Attribute and consequence audits pass.
After duality, arbitrary-carrier image gaps fall **28 → 27 per side**, and
fully settled rows rise **4654 → 4656**. Finite gaps remain **63 per side**,
with **4590** fully settled rows. The local export has **418 records** and
**257 generated consequences**. The explicit fine-spectrum result for the
long target is outside the 4694-law graph and is not counted among its
generated native-number arrows.

The analogous joined identity for E714's prospective division image was
unresolved in this pass. It is now **refuted by a nine-element commutative
quasigroup**, proved in `Equation714ImageCandidate.lean`; see the 2 November
follow-up below. The original bounded proof searches and small-model checks are recorded in
[`joined_inverse_images_20261023.json`](../data/parastrophes/joined_inverse_images_20261023.json);
timeouts have not been promoted to negative results.

## Independent parameters and patched subtraction (24 October 2026)

Three more exact left-division images are now proved on arbitrary carriers:

| Source | Canonical target | Defining identity |
|---|---|---|
| E1586 | E148963 (six operations) | `x=y*((z*(w*y))*((u*x)*x))` |
| E1370 | E307556419314087120878580960 (21 operations) | `x=y*(S(S(S(z*y)*y))*x)`, where `S(t)=t*t` |
| E695 | E101161666 (eight operations) | `x=(y*e(z))*((w*(x*w))*y)`, where `e(z)=(z*(z*z))*z` |

The free parameters in the E1586 identity express the independence of two
translation parameters. Short equational derivations prove left bijectivity
and both division transfers. E1370's image is exactly E127 together with
`x=y*((S(z*y)*y)*x)`. The two extra squarings force E127, which also makes
squaring an involution, so they disappear once cancellation is established.
The inverse multiplication is particularly short: `M(x,y)=D(D(x,x),y)`.
The forward division term is `D(x,y)=((x*x)*x)*y`. Forgetting the second
component of the target gives a new **E1370 → E127 term-structural arrow on
arbitrary carriers**, formalized in
[`DivisionImageConsequences.lean`](../equational_theories/Definability/DivisionImageConsequences.lean).
The exact correspondence with the long target also preserves labelled and
unlabelled model counts; no equivalence with E127 itself is asserted.

For E695, the eight-operation identity combines **E1155** with the assertion
that every `e(z)` is a right identity. E1155 alone is insufficient: subtraction
on three elements satisfies it, but its division is addition, which fails
E695. In the combined identity, a short equational calculation first forces
`y*e(z)=y`, recovering both component axioms. These imply left bijectivity and
recover the original operation under actual division. The same target
characterizes the divisions of E1710 models. This transfer proof assumes
actual division; the catalogue separately obtains all-carrier bijectivity
from E1492.

The new targets also have short explicit inverse terms: **`(x*(y*x))*x`**
for the E695/E1710 image, and **`(x*(x*x))*((x*y)*y)`** for the E1586 image.
Both are proved as uniform division witnesses in their respective modules.
The E1586 correspondence additionally has an explicit all-carrier
fine-spectrum theorem, `sameFineSpectrum1586_leftImage`.

A different construction supplies three negative results. On any abelian
additive group put `M(x,y)=-y` when `x=0`, and `M(x,y)=y-x` otherwise. This
changes only the zero row of subtraction. It satisfies **E1278, E1325 and
E1387**, and its left division is `D(x,y)=x+y` except in that zero row.
Given finitely many positive natural inputs and a fixed term, choosing a
large cyclic group makes every intermediate sum positive and smaller than
the modulus, so the exceptional row is never used. Consequently every
identity common to these finite division models holds in positive natural
addition, then in natural addition by shifting inputs and cancelling the
common shift, and finally in Boolean join. Boolean join has no left division.
Thus **none of these three finite division images can be characterized by a
single equation**, of any length. The argument actually rules out any set of
ordinary identities. The catalogue records the requested single-equation
consequence; duality gives the corresponding right-image negatives.

The proofs are in
[`Equation1586Image.lean`](../equational_theories/Parastrophes/Equation1586Image.lean),
[`Equation1370Image.lean`](../equational_theories/Parastrophes/Equation1370Image.lean),
[`Equation695Image.lean`](../equational_theories/Parastrophes/Equation695Image.lean), and
[`PatchedSubtraction.lean`](../equational_theories/Parastrophes/PatchedSubtraction.lean).
They use ordinary kernel checking, without sorries, native checking, or
external proof certificates. Solver searches are discovery aids only.

## Triality cores and finite group approximations (24 October 2026)

**E1525's left-division image has no single-equation characterization, even
among finite magmas.** This does not obstruct computing left division by a
term in the original E1525 operation; that positive result remains valid.

Let `s` be an automorphism of a group with `s³=id`. The twisted core
`M(x,y)=s(x*y⁻¹*x)` satisfies E1525 and has left division
`D(x,y)=x*(s²(y))⁻¹*x`. Use the free group on three generators, with `s`
cycling them. Reduced words that begin and end with the first generator
form a submagma under `D`: the middle word begins and ends with the inverse
of a different generator, so neither boundary cancels. Consequently
`length(D(x,y))=2*length(x)+length(y)`. This submagma lacks left division,
already proving the arbitrary-carrier obstruction.

This also proves a stronger fact about that particular infinite model:
**no term in `D` recovers `M`**, even if the term is chosen just for that
model. Every term evaluated at the first generator still begins and ends
there, whereas its original square is the second generator. This is
`TrialityCore.inverse_not_term`; it concerns recovery in the reverse
direction, so it does not change the positive division-term entry for E1525.
The finite approximation also proves
`TrialityCore.no_uniform_finite_inverse`: **no single inverse term works
across even this restricted family of finite division images**. Each finite
member has an inverse term by iterating its bijective rows; the needed
exponent cannot be bounded uniformly across the family.

For the finite result, any two distinct free-group elements can be separated
in a finite permutation group. The formal proof takes the finite set of
suffixes of a word and extends partial left translations to permutations.
Taking three rotated copies of such a representation preserves `s³=id`.
Thus any identity valid in all finite E1525 division images holds in the
free-group image, hence in positive integers with operation `2*x+y` by the
length formula. Shifting inputs extends it to nonnegative integers, which
map onto Boolean join by testing positivity. Join is finite and lacks left
division, contradicting any proposed characterization. The same argument
rules out characterization by any set of identities.

All steps are kernel-checked in
[`TrialityCore.lean`](../equational_theories/Parastrophes/TrialityCore.lean),
[`FreeGroupFiniteSeparation.lean`](../equational_theories/Parastrophes/FreeGroupFiniteSeparation.lean),
and [`FiniteTrialityCore.lean`](../equational_theories/Parastrophes/FiniteTrialityCore.lean).
There are no SAT certificates, native checks, or admitted claims in these
proofs. The finite separation lemma is independent of E1525 and is reusable.

Together these two rounds on 24 October reduce the applicable unknown
single-equation cells **per side** from **27 to 15** on arbitrary carriers
and from **63 to 50** on finite carriers. There are now **4676/4694** fully
settled arbitrary-carrier rows and **4612/4694** fully settled finite rows,
with **428** checked records. The detailed changes and unsuccessful research
branches are recorded in
[`independent_images_and_triality_20261024.json`](../data/parastrophes/independent_images_and_triality_20261024.json).

One further partial result is now formalized for **E872**. Its finite
left-division image is exactly the conjunction of **E614** and
**E162817**, `x=y*(c(x)*(y*x))`, where `c(x)=x*((x*x)*x)`. Under actual division,
`c(x)` recovers the original square. E614 then gives the first cancellation,
and the second identity gives the original E872 law. Conversely the second
identity makes every row surjective, hence bijective on a finite carrier.
The inverse multiplication is the explicit five-operation term
`M(x,y)=c(y)*(x*y)`.
This is `Eq872Image.characterizes_fin` in
[`Equation872ImageBasis.lean`](../equational_theories/Parastrophes/Equation872ImageBasis.lean).
The **single-equation** question is still open, so this result does not
decrease the counts above.

## Singular reductions: E882 and E907 (2026-10-26)

Three more characterization gaps are closed negatively: **E882's left-division
image and both E907 division images have no single defining equation, even on
finite carriers**. Duality gives the corresponding results for E2670 and E2700.
The finite right-quasigroup question for E907 remains open; its right-image
theorem concerns those models which actually possess right division.

The new mechanism uses a bad reduction of an otherwise valid family of division
operations. Write `D(x,y)=Px+Qy`, with commuting integer matrices. For E882 use
the rank-two algebra `Q²=-2`, `P=Q-1`. For E907 use the rank-three algebra
`Q³=2Q-2`, `P=1-Q`. These satisfy the original relations
`P²=-1-2Q` and `Q³=-2P`, `P²=PQ²-1`, respectively. Over every field of odd characteristic, `Q` is invertible,
and `M(x,y)=Q⁻¹(y-Px)` satisfies the indicated source law. This gives explicit
finite models of orders `p²` and `p³` for odd primes `p`. (The original four-
and six-coordinate constructions were reduced on 29 October.) Any identity common to
these finite division operations holds on the integer module: otherwise a
nonzero integer coordinate would vanish modulo arbitrarily large primes.
But modulo 2, the evaluation `P=1, Q=0` maps the operation onto two-element
left zero, `x*y=x`. Left zero has constant rows, so it cannot be anyone's left
division. This contradicts any proposed exact defining equation.

In fact the conclusion is stronger: every common identity of these left images
has the **same leftmost variable on both sides**. These are exactly the
identities satisfied by two-element left zero. Consequently even an arbitrary
collection of magma identities cannot characterize the images. For E907's
right image the dual statement preserves the rightmost variable. The general
`leftmost_of_prime_reductions` theorem records this invariant in Lean.

For E907, `P⁻¹=Q²-P` is integral too. Its opposite right division is
`D'(x,y)=(Q²-P)x-(Q²-P)Qy`, with the same bad reduction. Applying the argument
to opposite multiplication settles the right image. The same integer-transfer
argument also proves that **no single reverse term works throughout either
family**, although each individual finite model has a reverse term. These are
negatives about recovering multiplication from division; the existing forward
left-division terms for E882 and E907 are unaffected.

The reusable transfer and obstruction are in
[`ReductionImageObstructions.lean`](../equational_theories/Parastrophes/ReductionImageObstructions.lean).
The matrices, source identities, cancellation identities, and three registered
results are checked in
[`Equation882ImageObstruction.lean`](../equational_theories/Parastrophes/Equation882ImageObstruction.lean)
and
[`Equation907ImageObstruction.lean`](../equational_theories/Parastrophes/Equation907ImageObstruction.lean).
These use ordinary kernel proofs, including small coordinatewise ring
calculations, with no external certificates or `sorry`.

The catalogue now has **431 checked records**. Finite single-equation gaps fall
**50 → 47 per side**, and fully settled finite rows rise **4612 → 4614**.
Arbitrary-carrier counts remain **15 image gaps per side** and
**4676 fully settled rows**. The constructions, theorem references, and research
audit are recorded in
[`singular_reductions_20261026.json`](../data/parastrophes/singular_reductions_20261026.json).
Further E872 identity-compression searches and the finite E1518 square-cube
approach did not settle those questions.

## Controlled group triangles: E1719 and E1888 (2026-10-26)

**Neither division image of E1719 has a single-equation characterization on
arbitrary carriers.** Duality gives both negatives for E1888 as well. These
are four previously open cells. The finite image questions remain open.
The construction actually rules out characterization by any collection of
identities, because the images are not closed under submagmas.

Here is the underlying family. On a group, partition the elements into oriented
triangles with a turn permutation `s` satisfying

```
s³(x) = x,                 x · s²(x) · s(x) = 1.
M(x,y) = s²(x)⁻¹ · y⁻¹,
L(x,y) = y⁻¹ · s²(x)⁻¹,    R(x,y) = s(y⁻¹ · x⁻¹).
```

Then `M(x,x)=s(x)`, and a short cancellation proves E1719,
`x=M(M(y,y),M(M(x,x),y))`. The displayed `L` and `R` are its actual left and
right divisions. The turn need not be a group automorphism. This flexibility
is essential: restricting it to power maps or a single modified triangle
missed the obstruction.

For the countermodel, use the free group on generators `g₀,g₁,…`. Complete a
triangle partition one point at a time. When an uncovered point `a` is chosen,
choose a generator `gₖ`, with `k>0`, absent from every word used so far, and add

```
a  ↦  gₖ a⁻¹  ↦  gₖ⁻¹  ↦  a.
```

The fresh partners are distinct and unused. They also avoid two protected sets:
(1) `g₀` together with words starting negatively and ending positively;
(2) words starting with positive `g₀` and ending with a negative `gⱼ`, `j>0`.
Consequently every point of either protected set is eventually the **first**
point of an inserted triangle, and its second turn is `gₖ⁻¹`.

The first protected set is closed under `L`. There is no cancellation in
`L(x,y)=y⁻¹gₖ`, so its length is `|y|+1`; the element `g₀` is missing from every
row. For right division, take the set of words starting with positive `gᵢ`,
`i>0`, and ending with negative `g₀`. If `x,y` lie there, then
`z=y⁻¹x⁻¹` lies in the second protected set, and
`R(x,y)=s(z)=gₖz⁻¹` stays in the right-division subset. Its length is
`1+|x|+|y|`, so its columns miss the two-letter word `g₁g₀⁻¹`.
Both subsets inherit every identity of their ambient division operation, but
lack the required division themselves. This proves the two obstructions.

The same closed subsets prove **model-specific reverse term impossibility**:
even on this one infinite model, no binary term in `L` recovers `M`, and no
binary term in `R` recovers `M`. This concerns multiplication recovered **from**
division. The already-established terms giving the divisions **from** an
E1719 multiplication remain valid.

The generic completion theorem is in
[`TriangleCompletion.lean`](../equational_theories/Parastrophes/TriangleCompletion.lean),
and the group model, word calculations, reverse-term obstructions and catalogue
registrations are in
[`Equation1719ImageObstruction.lean`](../equational_theories/Parastrophes/Equation1719ImageObstruction.lean).
Everything uses ordinary Lean proofs; there are no `sorry`s, native checks or
external proof certificates. The research record also includes unsuccessful
E1286 inverse-term searches and the enlarged matrix and group-family scans:
[`controlled_triangles_20261026.json`](../data/parastrophes/controlled_triangles_20261026.json).

After propagation, arbitrary-carrier image-characterization gaps fall
**15 → 13 per side**, and fully settled rows rise **4676 → 4678** out of 4694.
There are **433 checked catalogue records**. Finite counts remain **47 image
gaps per side** and **4614 fully settled rows**. The parastrophe build and all
17 catalogue/viewer tests pass; the local website data has been refreshed.

The finite case needs additional work: this countable completion is not a
finite completion theorem. A possible next route is to embed its finite partial
triangle configurations into finite examples while preserving the relevant term
evaluations; that embedding has not been proved here.

## Singular exceptional rows: E473 and E879 (2026-10-26)

**Neither E473 nor E879 has a single-equation characterization of its finite
left-division image.** Duality settles the finite right-image questions for
E3056 and E2650. In fact, no set of identities characterizes these images.
These are four new finite cells; their arbitrary-carrier rows were already
settled by failures of the relevant bijectivity property.

The new idea is to adjoin a right zero `∞` to a Gaussian affine magma:
`M(x,∞)=∞`, and `M(∞,y)=F(y)` on old elements. Its division has the same form,
with old left division in place of multiplication and the inverse permutation
`H=F⁻¹` in the exceptional row. We arrange for the division formulas to have
integer coefficients while the multiplication needs division by 2.

* **E473:** on one Gaussian coordinate, take
  `M(x,y)=3i*x-i*y`, `D(x,y)=3*x+i*y`, and `H(x)=2i*x`.
  The square map is also `H`, so `F(H(x))=x` verifies the mixed E473 instance
  `F(M(x,F(M(x,x))))=x`. The finite models have order `1+p²` for odd primes p.
  Modulo 2 the exceptional division row is constant, giving a **five-element**
  magma outside the division image.
* **E879:** use two Gaussian coordinates with
  `M(x,y)=-x+i*y`, `D(x,y)=-i*(x+y)`, and
  `H(u,v)=((i-1)*v,u)`. Here `H²` is the old square map, so
  `F(F(M(x,x)))=x` verifies the mixed E879 instance. The finite models have
  order `1+p⁴`. Modulo 2, multiplication by `i-1` has a nonzero kernel, so
  the exceptional row has a collision in the **17-element** reduction.

Every common identity of the odd-prime division models holds over the
integers: the difference of two integer coordinates cannot vanish modulo all
odd primes unless it is zero. Reducing that identity modulo 2 then forces it
on the bad finite magma. Thus no identity, or collection of identities, can
separate the actual finite images from that nonimage. This is different from
a large finite model search: the proof handles identities of arbitrary length.

The same argument proves **no uniform reverse term** for either family: there
is no fixed term in division recovering the original multiplication across all
odd primes. This does not contradict model-dependent inverse terms on finite
carriers, or the catalogue's forward terms that recover division from source
multiplication.

The common transfer argument is in
[`OptionReductionImage.lean`](../equational_theories/Parastrophes/OptionReductionImage.lean).
The two families and their registrations are in
[`Equation473ImageObstruction.lean`](../equational_theories/Parastrophes/Equation473ImageObstruction.lean)
and
[`Equation879ImageObstruction.lean`](../equational_theories/Parastrophes/Equation879ImageObstruction.lean).
The proofs use the ordinary Lean kernel, with no `sorry`, native check or
external certificate. The local website export now has **435 checked records**.
Finite image-characterization gaps fall **47 → 45 per side**, and fully settled
finite rows rise **4614 → 4618**. Arbitrary-carrier counts stay at **13 image
gaps per side** and **4678 fully settled rows**.

This pass also tested E1518's conjectured three-cycle square map in several
larger structured families. All 91 tested scalar central-extension systems
preserved it; permutation-fibre searches over four fixed base models also
found no counterexample. A noncommutative group-permutation construction was
ruled out for the tested distinguished elements in groups of orders 10, 12,
14, 21 and 24, and timed out at order 39. These are bounded computational
observations, not a proof of the general conjecture. An apparent small E879
reverse term was refuted by an explicit six-element source model. The formulas,
models, search limits and outcomes are saved in
[`exceptional_rows_20261026.json`](../data/parastrophes/exceptional_rows_20261026.json).

## E872: the boundary of affine constructions (2026-10-27)

**No additional catalogue cells closed in this pass.** E872's finite left
division image still has a proved two-equation basis, with a single-equation
characterization unresolved. The new result explains a limitation of affine
examples and rules out a tempting shortcut for compressing that basis.

For any abelian group, suppose `x*y = A(x)+B(y)+c` satisfies E872. The additive
endomorphisms A and B need not commute. Expanding the law at zero gives

```
A + B²A = 0
BA² + BAB + B³ = 1
(1 + B + B² + BA)(c) = 0.
```

Multiply the second identity by B and use the first to obtain
`A²+AB = B⁴-B`. Substitution eliminates A and gives
`(B³-1)(B²+1)=0`, hence `B¹²=1`. The sum of the first twelve powers of B
annihilates both `A(x)` and c, so **every row has order dividing twelve**.
This holds on arbitrary carriers, including infinite abelian groups.

However, a seven-element E872 model has row zero
`[1,2,3,4,0,5,6]`: a five-cycle through its diagonal entry. It therefore has
**no affine representation over any abelian group**, even after relabelling.
Both the general theorem and this counterexample are checked in
[`Equation872Affine.lean`](../equational_theories/Parastrophes/Equation872Affine.lean).
The module builds in about six seconds; its axiom audit contains only Lean's
standard axioms, with no `sorry`, native check, or external certificate.

For the image basis, put `c(x)=x*((x*x)*x)`. Rewriting this core with the two
known identities produced 22,343 candidate terms; 1,140 survived the initial
countermodel filter. All survivors now have explicit countermodels of order
at most six. A separate search constrained by affine examples suggested the
core `L_x^11(x)`, but the seven-element nonlinear source refutes its required
forward identity. These are failures of specific candidates, not a proof that
no single equation exists. The models, search limits, and additional bounded
attempts on E1518 and matrix constructions are saved in
[`e872_affine_boundary_20261027.json`](../data/parastrophes/e872_affine_boundary_20261027.json).
Counts remain **13 arbitrary-carrier image gaps per side**, **45 finite image
gaps per side**, and **4678 / 4618 fully settled rows**, respectively.

## Twisted cycles: E1492 and E1496 (2026-10-27)

**Neither division image of E1492 or E1496 can be characterized by a single
equation on arbitrary carriers.** The same holds for their duals E2135 and
E2146. These are eight newly closed cells. The construction actually rules out
any set of defining identities, by exhibiting a submagma outside the image.
It does not settle the corresponding finite questions.

The carrier is a right identity e together with countably many copies of the
integers. Let `C(i,n)=(i,n+1)` and `C(e)=e`. We construct a quasigroup D with

```
D(x,e) = x             D(e,x) = C(x)
D(z,D(y,z)) = C(y).
```

A multiplication triple `(a,b,c)` forces `(b,c,C(a))` and then
`(c,C(a),C(b))`; three rotations shift the entire triple by C. At each stage,
fill an undefined product with an element from a fresh integer orbit, and add
all shifted rotations of that triple. Only finitely many orbit labels have
been used, so a fresh one is available. Filling all pairs gives a total
operation; the cyclic identity and the bijectivity of C give both inverse
identities for its left division

```
M(x,y) = D(C⁻¹(y),x).
```

Here `M(x,x)=e` and `M(y,e)=C(y)`. Consequently
`M(M(y,x),M(y,M(z,z)))=M(M(y,x),C(y))=x`, which is E1496.
Setting z=y also gives E1492.

The key control is to give each fresh output the smaller of its inputs'
integer indices. All shifted rotations preserve the inequality
`index(output) ≥ min(index(left),index(right))`. Thus e and the nonnegative
halves of all the orbits form a submagma of D. Its row at e is the upward
shift, which misses every element at index zero. It therefore lacks left
division, although it inherits every identity of D. This also proves that
even on this one infinite model no term in D recovers M: terms preserve the
submagma, whereas `M(e,(0,0))=(0,-1)` leaves it.

The completion and obstruction are checked in
[`TwistedCycleCompletion.lean`](../equational_theories/Parastrophes/TwistedCycleCompletion.lean)
and
[`Equation1496ImageObstruction.lean`](../equational_theories/Parastrophes/Equation1496ImageObstruction.lean).
The new modules take about **six and five seconds**, respectively, to build.
The axiom audit contains only Lean's standard axioms; no `sorry`, native
check, SAT certificate, or external theorem prover is needed.

After the local website export, arbitrary-carrier image gaps fall
**13 → 9 per side**, and fully settled rows rise **4678 → 4682**.
Finite counts stay at **45 image gaps per side** and **4618 fully settled
rows**. There are **437 checked records**. Research details and the final
inventory are saved in
[`twisted_cycles_20261027.json`](../data/parastrophes/twisted_cycles_20261027.json).

## Prescribed twisted cycles: E1695 and E880 (2026-10-27)

The next pass closes **six more arbitrary-carrier image cells**: both sides
for E1695 and its dual E1932, and the left side for E880 and right side for
its dual E2707. None of these images can be characterized by a single
equation, or even by a set of identities. Their finite counterparts remain
open.

The completion now allows a prescribed collection of products within each
block. Use countably many integer grids, with vertical shift C and horizontal
shift T. Before filling any other products, prescribe the following pairs
and all their shifted cyclic consequences:

| Source law | Prescribed products in H | Source operation M | Actual left division |
|---|---|---|---|
| E1695 | `H(a,Ca)=Ta`, `H(a,Ta)=C²a` | `H(C⁻¹y,x)` | `H(x,y)` |
| E880 | `H(a,Ca)=Ta`, `H(a,a)=C²a` | `C⁻¹(H(x,y))` | `H(y,x)` |

In both cases the completed H satisfies `H(z,H(y,z))=C(y)`. The prescribed
triples have no conflicting products and preserve nonnegative heights.
Every other missing product is filled with a fresh block at the smaller
input height, as in the E1496 construction. Only finitely many blocks have
been used for these added products at each stage; the prescribed products
stay within individual blocks, so they cannot clash with the new mixed
products. The generic completion proof handles both choices of prescribed
products.

For **E1695**, the source square is `M(y,y)=T(C⁻¹y)`, and hence
`M(M(y,y),y)=C(y)`. The cyclic identity then gives
`M(M(y,x),M(M(y,y),y))=x`. In the nonnegative submagma of its division,
the row at a height-zero point a misses a: the unique preimage is
`M(a,a)=T(C⁻¹a)`, of height −1.

For **E880**, the source square is `M(y,y)=C(y)`. Consequently
`M(y,M(M(x,y),M(x,y)))=C⁻¹(H(y,H(x,y)))=x`.
Its left division exchanges H's arguments. In its nonnegative submagma,
the row at a height-zero point a misses C(a): the unique preimage is
`M(a,C(a))=T(C⁻¹a)`, again of height −1.

The files are
[`SeededTwistedCycleCompletion.lean`](../equational_theories/Parastrophes/SeededTwistedCycleCompletion.lean),
[`Equation1695ImageObstruction.lean`](../equational_theories/Parastrophes/Equation1695ImageObstruction.lean),
and
[`Equation880ImageObstruction.lean`](../equational_theories/Parastrophes/Equation880ImageObstruction.lean).
The E1695 file also proves that no term in the division operation recovers
the source multiplication on this one model. These are ordinary Lean proofs
without `sorry`s, native checks, or external proof certificates.

After closure and the local website export, arbitrary-carrier image gaps
fall **9 → 6 per side**, and fully settled rows rise **4682 → 4686**.
Finite counts remain **45 image gaps per side** and **4618 fully settled
rows**. The export contains **439 checked records**. Details are saved in
[`seeded_twisted_cycles_20261027.json`](../data/parastrophes/seeded_twisted_cycles_20261027.json).

## Finite image gaps: closure and inverse-term searches (2026-10-27)

**No additional finite image-characterization cells closed in this pass.**
There remain **45 gaps per side** and **4618 fully settled finite rows**.

There is now a general Lean proof of why the recent submagma obstructions
cannot simply be made finite. For **every** source law and either side, its
actual division image is closed under finite submagmas and finite homomorphic
images. The ambient or covering algebra may even be infinite. On a finite
submagma, translations inherit injectivity, which gives surjectivity. On a
finite quotient, they inherit surjectivity, which gives injectivity. A
homomorphism between division algebras also preserves their inverse operations,
so the original source identity transfers. These results are in
[`FiniteImageClosure.lean`](../equational_theories/Parastrophes/FiniteImageClosure.lean),
with no `sorry` or external certificate; the full parastrophe build passes.

The finite searches concentrated on **E1085, E1112, E1312 and E1315**. They
looked for terms recovering multiplication **from division**, rather than the
forward division terms already recorded in the table. Several candidates passed
the initial finite and affine samples, but explicit nonlinear models of orders
4–8 refuted them. Ten such candidate refutations have been retained. After
adding those models, an exact Python search found no inverse term with at most
nine operations for any of the four laws. This is a bounded computational
result, not a Lean theorem or an obstruction to all longer terms.

The new reusable search evaluates subterms through eight operations, then
solves `D(u,v)=M(x,y)` for the required vector of values of v using
`v=M(u,M(x,y))`. A lookup replaces the quadratic search over pairs of subterms.
It additionally tests candidates through seventeen operations when both root
subterms have size at most eight; it does **not** exhaust all seventeen-operation
terms. Inputs and results are saved in
[`finite_images_20261027.json`](../data/parastrophes/finite_images_20261027.json).
For example:

```sh
python3 scripts/parastrophe_inverse_term_search.py \
  data/parastrophes/finite_images_20261027.json 1112
```

The affine scan of 2,304,960 assignments over two-element bases gave no new
singular-reduction family. The E872 search generated 364 unary and 931 mixed
insertions and saved several finite counterexamples. **Correction, 2026-10-28:**
its known-countermodel filter was reversed, so the earlier assertion that all
those candidates were refuted was incorrect. The explicit counterexamples
remain valid, but coverage of the candidate list was incomplete. This was a
scratch-search error; no Lean theorem or catalogue status depended on it.

## Finite cross-inverse families and the remaining image gaps (2026-10-27)

**The finite image counts are unchanged: 45 gaps per side, 4618 fully
settled rows.** This pass does, however, give a symbolic finite construction
with unbounded division-row periods for E1492 and E1496. The construction and
the unboundedness theorem are fully checked in
[`CrossInverseLoops.lean`](../equational_theories/Parastrophes/CrossInverseLoops.lean).
There are no stored multiplication tables or external proof certificates.

Over any field K of characteristic different from 3, define

```
f(x,y) = 0             if x=0 or y=0,
         x             if x+y=0 and neither input is zero,
         (x-y)/3       otherwise.
P((x,a),(y,b)) = (x+y, a+b+f(x,y)).
J(x,a) = (-x,-a-x).
```

The key calculation is `f(x,y)+f(x+y,-x)=x`. It implies
`P(P(u,v),J(u))=v`; cancellation also gives `P(u,P(v,J(u)))=v`.
The operation P has identity `(0,0)`, and J is an automorphism. Thus P is a
**cross-inverse loop**. Its inverse map satisfies
`J²(x,a)=(x,a+2x)`, so over F_p, for p≥5, its cycle through `(1,0)` has
length 2p. This is a useful contrast with constructions whose inverse maps
have a fixed, small period.

On the Cartesian square of this loop, put `C(u,v)=(v,J(u))`. With P applied
coordinatewise, set `D(a,b)=P(a,C(b))`. The crossed-inverse identities give
`D(z,D(y,z))=C(y)`, while D has right identity e and `D(e,y)=C(y)`.
Its left division is `M(x,y)=D(C⁻¹(y),x)`. All M-squares equal e, and
`M(x,e)=C(x)`; substitution now proves E1496, and hence E1492. Both M and D
are quasigroups. Over F_p this produces **p⁴-element models**. Lean proves
that C has exact period **4p** on a specified element when p is odd, and that
for every positive exponent n some finite E1496 model has a division row
whose n-th iterate is not the identity. For p=5 this gives a 625-element
model with a division row containing a 20-cycle.

This rules out a universal row-period shortcut. It **does not** refute
uniform recovery by an arbitrary term: such a term can mix rows and nest
operations. Nor does it resolve finite single-equation characterization.
The existing infinite submagma obstruction still needs a separate argument
to yield a finite-image obstruction. The order p⁴ is already in the known
spectra; the new information concerns the internal operations.

Cross-inverse loops and long inverse cycles are classical; the literature
connection was checked against A. D. Keedwell, *Crossed-inverse quasigroups
with long inverse cycles and applications to cryptography* (1999),
[Australasian Journal of Combinatorics 20, 241–250](https://ajc.maths.uq.edu.au/pdf/20/ajc-v20-p241.pdf).
The normalized central-extension formula above is verified directly here;
no external existence theorem is assumed. One must distinguish loops from
Keedwell's simpler affine **quasigroup** constructions: those need not have
an identity and cannot be substituted into the loop argument unchanged.

Other approaches in this pass gave no closure: an audit of all six
parastrophes found no missing characterization obtainable by composing the
currently known catalogue characterizations; noncommuting coordinate-word
constructions gave only the already-known E1525 family. The 1180-candidate
E872 compression run inherited the pruning error corrected on 2026-10-28:
its saved refutations remain valid, but it did not exhaustively reject the
candidate list. An E1518 permutation search on
the group of order 39 stopped at its conflict budget, with no conclusion.
Parameters and outcomes are recorded in
[`finite_cross_inverse_loops_20261027.json`](../data/parastrophes/finite_cross_inverse_loops_20261027.json).

## Corrected finite-image search and a shape theorem (2026-10-28)

**No finite characterization cells closed: 45 remain per side, with 4618
fully settled finite rows.** An audit found that the old E872 scratch searches
had reversed their countermodel filter: they discarded candidates that failed
a known bad model, instead of those that held in one. The saved individual
counterexamples were valid, but the purported exhaustive search coverage was
not. No Lean theorem or catalogue status relied on that search claim.

The replacement [replay script](../scripts/parastrophe_e872_compression.py)
validates that every supplied bad model really fails the exact image basis,
keeps an account of every candidate, and has regression tests for the pruning
direction. With 80 independently checked bad tables and explicit cyclic
countermodels, the corrected replay now **does** refute all 364 unary,
931 mixed, and 1180 unrestricted candidates from the earlier campaigns,
as well as all **20,827** candidates in the expanded three-insertion campaign.
These lists overlap and their counts should not be added. Two new six-element
tables disposed of the last fourteen candidates in the expanded campaign.
Other searches using extra derived identities were partial; no exhaustive
claim is made for them.

There is also a new necessary condition proved in Lean. **Any single identity
characterizing this finite image must, up to exchanging its sides, have the
form `x = A*(B*(C*x))`**, with arbitrary terms A, B, C. Both sides cannot be
composite, because the two-element constant magma would satisfy the identity.
Right projection forces the rightmost variable to be x. A right-unary
three-cycle, which is a genuine division image, forces the number of right
branches to be a multiple of three. Conversely, a right-unary cycle whose
length equals that branch count satisfies the candidate, and belongs to the
image only when that length divides three. Thus the count is exactly three.
This gives explicit cyclic countermodels for many large candidates, including
seven that the bounded solver searches had left unresolved.

[`Equation872ImageShape.lean`](../equational_theories/Parastrophes/Equation872ImageShape.lean)
also proves a reusable finite consequence: if every inverse row factors
pointwise through the row indexed by `T(y)`, those indexed rows cover all rows.
The proof uses a finite set of distinct row functions and an injective map on
that set; it does not identify elements that happen to have identical rows.
Both results are ordinary kernel proofs without `sorry` or native checking.
The image-basis module now also proves that, writing
`c(x) = x*((x*x)*x)` in the division operation, **`c(c(x)) = x*x`**.
Thus the recovered original square map is a compositional square root of the
division square map. This identity holds in actual images on arbitrary carriers;
the finite two-equation basis implies it as well.

A separate E1112 search reached 3,342,672 distinct term-value signatures and
found a nineteen-operation candidate for recovering multiplication from
division. A new six-element E1112 model refuted it: at `(x,y)=(0,1)`, the
source product is 3 and the candidate gives 1. Adding that table and repeating
the search eliminated every inverse term with at most ten operations on the
saved samples. This is a bounded computational result, not a theorem excluding
arbitrary inverse terms.
An expanded run reached twenty million signatures and found another
nineteen-operation candidate. A seven-element E1112 model refuted that candidate
at `(x,y)=(0,1)`, where the product is 1 and the candidate gives 0. The expanded
run did not complete its ten-operation subterm layer, so it does **not** extend
the exhaustive bound to eleven-operation inverse terms. Both refuting models
were checked independently of the model finder and are saved in the audit.

The models, corrected coverage, candidate refutations, and theorem references
are saved in
[`e872_compression_audit_20261028.json`](../data/parastrophes/e872_compression_audit_20261028.json).
The replay can be reproduced with:

```sh
python3 scripts/parastrophe_e872_compression.py \
  data/parastrophes/e872_compression_audit_20261028.json \
  --output /tmp/e872-replay.json
```

## Finite-image follow-up: smaller obstructions and an affine limitation (2026-10-29)

**The characterization counts are unchanged: 45 finite gaps per side and
4618 fully settled finite rows.** This pass strengthens the supporting results
and audits a larger E872 search; it does not mark a surviving candidate as a
characterization.

The E882 and E907 obstruction families now use half as many coordinates.
For E882, choose `Q²=-2` and **`P=Q-1`**: the required relation
`P²=-1-2Q` follows immediately. For E907, choose **`Q³=2Q-2` and `P=1-Q`**:
these give `Q³=-2P` and `P²=PQ²-1`. The latter choice comes from factoring
`Q⁶+2Q⁵+4` as `(Q³-2Q+2)(Q³+2Q²+2Q+2)`. The existing Lean files now prove
the same characterization negatives and uniform reverse-term negatives using
models of orders **p² and p³**, in place of p⁴ and p⁶. Both constructions still
specialize onto two-element left zero at characteristic 2. This supplies smaller
families witnessing the existing obstructions.

The E907 source also works over any commutative ring with a half. Writing
`2h=1`, its operation is

```
x ◇ y = (y₀+y₁−x₁, x₁+y₂−x₂, x₂+h(x₀−y₀)).
```

It is idempotent, and the E907 identity reduces to three multiples of `2h−1`.
Taking `R=Z/nZ`, for any odd n, proves **every odd cube n³ lies in the E907
spectrum**, including 125. This family is now included in the catalogue lower
bound and transfers to the dual E2700. The independent, kernel-checked proof is
[`Spectrum/Equation907/Cubes.lean`](../equational_theories/Spectrum/Equation907/Cubes.lean);
it checks three coordinates rather than enumerating pairs of elements.

For E872, the cross identity together with `c(c(x))=x*x` is now another
**exact finite image criterion**. The new implication is particularly short.
Apply the cross identity at `(c(x),x)` and replace `c(c(x))` by `x*x`:

```
x*((x*x)*(x*c(x))) = c(x) = x*((x*x)*x).
```

Cancel the rows indexed by x and x*x to obtain `x*c(x)=x`, the other identity
in the original basis. Only row injectivity is needed for this step; in the
finite criterion, the cross identity already makes all rows surjective.
The lemmas are `unit_of_core_square` and `characterizes_core_square_fin` in
[`Equation872ImageBasis.lean`](../equational_theories/Parastrophes/Equation872ImageBasis.lean).

There is also a proved limitation of the scalar affine route for E1112.
Write division as `D(x,y)=p*x+q*y` over a field, where q is nonzero. Its source
is `M(x,y)=(y-p*x)/q`. Substituting `(1,0)` and `(0,1)` in E1112 gives
`p²+q²=q⁴` and `p(q³-pq+1)=0`. Eliminating p yields

```
q * (q⁵ + 2q⁴ - q³ - 2q² + q) = 1.
```

Thus the coefficient inverse is an integer polynomial in q. Any reduction
preserving this identity preserves invertibility, blocking this way of obtaining
a singular bad reduction. This is a statement about the ambient ring operations,
**not a magma term** recovering multiplication. The complete calculation is in
[`Equation1112Affine.lean`](../equational_theories/Parastrophes/Equation1112Affine.lean).
A bounded scan of 4,513,880 pairs of integer 2-by-2 matrices, without assuming
they commute, found no new family for the 45 open cases; it found E882 as a
positive control. Symbolic scalar elimination found no new singular reduction
either. These search results are recorded separately from the Lean proofs.

The E872 rewrite audit now generates all 65,692 eligible candidates in its
three-step, 35-operation campaign. New finite model searches and right-zero
extensions of known images supply additional checked refutations. The final replay
refutes **65,504 candidates**, leaving **188 unresolved**, with a shortest survivor
of 20 operations. The 169,272 extension permutations produced 206 candidate
refutations; the pooled replay also uses separately found finite models. Every
eligible candidate is accounted for by the replay script; remaining candidates and the
precise bounded search coverage are in
[`finite_image_followup_20261029.json`](../data/parastrophes/finite_image_followup_20261029.json).
The rewrite family is not the set of all identities of that length. A timeout
or an unsuccessful theorem-prover run is not a refutation or a proof.

```sh
python3 scripts/parastrophe_rewrite_replay.py \
  data/parastrophes/finite_image_followup_20261029.json \
  --output /tmp/e872-rewrite-replay.json
```

## E872: commuting rows and two new finite obstructions (2026-10-29)

**The catalogue still has 45 finite image-characterization gaps per side and
4618 fully settled finite rows.** The following results narrow the E872 search;
they do not settle whether one equation characterizes its finite division image.

One of the previously shortest surviving candidates, research index **3652**, has 20 operations.
It is now proved to hold in every actual E872 left-division image, on arbitrary
carriers. Its converse is proved when the candidate division's left translations
are **commuting involutions**. This includes operations `D(x,y)=t(x)+y` on any
abelian group of exponent two, with an arbitrary function t. The proof sets
`S(x)=x*x` and `U(x)=S(x)*x`. The candidate identifies certain left translations
with `L_y ∘ U`; commutation and involutivity then make U a central involution.
Evaluating the candidate's index at `(x,x)` gives `L_U(x)=L_x ∘ U`.
Together these force `U(x)=x`, and both identities in the exact image basis
follow. See `characterizes_commuting_involutions` in
[`Equation872ImageCandidate.lean`](../equational_theories/Parastrophes/Equation872ImageCandidate.lean).
The unrestricted converse is false, as the second construction below proves.

A different construction refutes four of the 22-operation candidates. On two
copies of `Z/3Z`, put

```
(a,u)*(b,v) = (b,v+1)  if a=b,
             (b,u-v)  if a≠b.
```

The four identities hold, but the cross identity from the exact basis fails
between the two fibres. The Lean proof works more generally over any abelian
group with a nonzero element e satisfying `3e=0`: use `v+e` in the first branch.
Splitting only the Boolean coordinates reduces the candidate identities to
`3e=0`, while failure of the cross identity reduces to `e≠0`. Thus verification
does not enumerate all triples in the six-element model. The declarations
`folded_satisfies_A`, `folded_satisfies_B`, and `folded_not_image` are in
[`Equation872ImageCandidateCounterexample.lean`](../equational_theories/Parastrophes/Equation872ImageCandidateCounterexample.lean).
The refuted research indices are 10613, 10881, 11985, and 12992; these are
candidate indices, **not equation numbers**.

The 20-operation candidate 3652 itself has a **25-element quasigroup
counterexample**. On `(Z/5Z)²`, define

```
(a,b)*(c,d) = (a+3d, b+c).
```

Equivalently, this is `D(x,y)=x+qy` over the field of 25 elements, with `q²=3`.
Both sides have bijective translations. Substitution in candidate 3652 gives
coordinate errors divisible by 5, so the candidate holds. But the cross identity
at `x=(0,0)`, `y=(1,0)` would say `(0,0)=(4,0)`. Thus the model is not an E872
left-division image, even though it is a quasigroup. The symbolic Lean proofs
are `field25_satisfies`, `field25_not_image`, `field25_quasigroup`, and
`refutes_candidate` in the same counterexample file; they need no large finite
enumeration. This model refutes six candidates, including 3652 and its
variable-renamed form 4374.

The discovery highlights a limitation of characteristic-zero calculations.
For a scalar affine operation `D(x,y)=p*x+q*y+s`, a rational Gröbner-basis
calculation incorrectly suggested a general implication from the candidate to
the exact basis. Checking the coefficient denominators exposed exceptional
components in characteristics 5 and 32537. The characteristic-5 component
`p=1`, `q²=3`, `s=0` gives the small model above. There is also a scalar
counterexample on `Z/32537Z`, with `p=15060`, `q=24114`, `s=0`, recorded in the
replay. No characteristic-zero calculation is used as evidence for a finite
characterization.

Replaying the same 65,692-candidate campaign with these models now refutes
**65,514 candidates**, leaving **178**, down from 188. An exhaustive search of binary fibres
over the six three-element quotient images found no further counterexamples:
it checked all 262,144 parameter choices per quotient, covering all
row-bijective operations with those quotient and fibre data. The new model
instead came from three-element affine fibres over a two-element quotient.
Additional bounded translation, noncommutative-group, and indexed-ring searches
did not settle another catalogue cell. Failed searches and theorem-prover
timeouts are recorded as inconclusive, separately from the Lean theorems.

The checked tables, search scopes, proof references, and updated survivors are in
[`e872_commuting_rows_20261029.json`](../data/parastrophes/e872_commuting_rows_20261029.json).
Reproduce the candidate accounting or the binary-fibre search with:

```sh
python3 scripts/parastrophe_rewrite_replay.py \
  data/parastrophes/e872_commuting_rows_20261029.json \
  --output /tmp/e872-latest-replay.json
python3 scripts/parastrophe_e872_block_search.py \
  data/parastrophes/finite_image_followup_20261029.json \
  --output /tmp/e872-blocks.json
```

## Exact bases and nilpotent affine countermodels (2026-11-01)

The E872 search now has **148 surviving candidates, down from 178**. Three
25-element quasigroups refute the additional 30 candidates, with all 30
refutations proved in Lean. No single-equation characterization cell is closed:
there are still 45 finite gaps per side. The ten surviving 20-operation
candidates are unaffected by this pass.

The new constructions use the dual-number ring `R = F5[ε]/(ε²)`, where ε is
nonzero but ε²=0. On its 25 elements the operations are:

| Operation on R | Extra property | Candidates refuted |
| --- | --- | ---: |
| `(3+ε)x + (3+ε)y` | Commutative quasigroup | 6 |
| `(-1+ε)x + (2-ε)y` | Idempotent quasigroup | 6 |
| `(3+ε)x + 3y + 1` | Quasigroup | 18 |

All the coefficients multiplying x and y are units. Nevertheless, each model
fails the exact E872 image basis. They were found by searching matrix affine
operations and then affine operations over truncated polynomial rings, including
constant offsets. The first two models appeared in an unrestricted 2-by-2
matrix search over F5; their matrices happen to commute. Their nonzero
nilpotent parts are what searches over fields alone miss. A later search over
`F5[t]/(t³)` found the third model, which reduces to two coordinates.

Verification is symbolic. For `D(x,y)=p*x+q*y+s`, every three-variable term has
four coefficients: those of x, y, z, and the constant. Structural induction
proves that computing these coefficients determines the value on every
assignment. The new checker in
[`AffineIdentityCertificate.lean`](../equational_theories/Parastrophes/AffineIdentityCertificate.lean)
works over any commutative ring. For the concrete dual-number models, ordinary
kernel `decide` checks four elements of a 25-element ring per identity; it does
not enumerate 25³ assignments. The 30 candidate terms, their checks, their
non-image proofs, and the quasigroup properties are in
[`Equation872NilpotentCandidates.lean`](../equational_theories/Parastrophes/Equation872NilpotentCandidates.lean).
The whole concrete module builds in about nine seconds in the current workspace.

### Recording several defining equations

`CharacterizesBasis scope L side targets` records an exact characterization by
a finite list of identities. The new `@[parastrophe_basis]` attribute accepts
only unconditional, kernel-proved theorems of this type and exports the actual
identities and theorem location. These records are separate from the
`SingleEquation` question. In particular, a two-equation basis never turns that
question into a proved positive. The initial records are:

| Source and division | Scope | Known basis |
| --- | --- | --- |
| E872, left | Finite | Two identities; two alternative pairs recorded |
| E872, left | Arbitrary carriers | Three identities |
| E695, left | Arbitrary carriers | Two identities, shorter than its known single identity |
| E1710, left | Arbitrary carriers | The same pair, for the image of models admitting left division |
| E1370, left | Arbitrary carriers | Two identities, shorter than its known single identity |

For E872, write `c(x)=x*((x*x)*x)`. The familiar finite pair is

```
x = x*c(x),
x = y*(c(x)*(y*x)).
```

The original multiplication, whenever the candidate really is an image, is
`M(x,y)=c(y)*(x*y)` even on infinite carriers. The cross identity supplies one
inverse law. Adding the other inverse law,

```
c(x*y)*(x*(x*y)) = y,
```

therefore gives an exact three-equation characterization on arbitrary carriers.
The proof constructs M by that term and verifies both division laws, then
recovers E872. Finiteness makes the extra inverse law automatic in the
two-equation criterion. We have not shown that it is necessary on arbitrary
carriers. See `multiplication_eq` and `characterizes_all` in
[`Equation872ImageBasis.lean`](../equational_theories/Parastrophes/Equation872ImageBasis.lean).

The typed catalogue is
[`ImageBasisCatalogue.lean`](../equational_theories/Parastrophes/ImageBasisCatalogue.lean).
The website's existing characterization cells now show a supplementary
“2-equation basis” or “3-equation basis” link. The details display each identity
and its proof; the one-equation status remains independent. Basis evidence
transfers through duality, restriction to finite carriers, and ordinary
implication equivalence using exported Lean rules. A shorter finite basis
takes display priority over an inherited longer one. All alternatives remain
in the export's additive `imageBases` field; old bundles without it remain valid.

The research record, including the precisely bounded matrix and local-ring
searches, is
[`e872_image_basis_followup_20261101.json`](../data/parastrophes/e872_image_basis_followup_20261101.json).
Reproduce the candidate accounting and the local-ring search with:

```sh
python3 scripts/parastrophe_rewrite_replay.py \
  data/parastrophes/e872_image_basis_followup_20261101.json \
  --output /tmp/e872-replay.json
python3 scripts/parastrophe_affine_image_scan.py \
  data/parastrophes/e872_commuting_rows_20261029.json \
  --modulus 5 --dimension 3 --family local --output /tmp/e872-local.json
```

## Affine countermodels leave one candidate pattern (2026-11-01)

A further E872 pass reduces the **148 surviving candidates to two**, forming
**one pair under variable renaming**. All **146 additional refutations are
proved in Lean**. The complete replay now refutes **65,690 of 65,692** eligible
identities. These are the candidates generated by the recorded three rewrite
rounds, with at most 35 operations, not all possible identities. No unrestricted
single-equation characterization has been proved or disproved by this pass;
the finite catalogue still has **45 image-characterization gaps per side**.
All ten previously surviving 20-operation identities have now been refuted.

### One family supplies all 144 counterexamples

Use a commutative ring with an element `i` satisfying `i²=-1`, and put

```
D(x,y) = (1-i)*x + i*y + 1.
```

Evaluating any of the 148 proposed right-hand sides over the Gaussian integers
produces `x + a + b*i`: its three variable coefficients are exactly `(1,0,0)`.
The constant term, which the earlier zero-offset searches could not detect,
provides the obstruction. Factor its norm `a²+b²`, and reduce modulo a suitable
Gaussian prime. Then the candidate holds, while the necessary image identity
`x=D(x,c(x))` fails by the nonzero constant `2*i-1`. For example, over F13,
`D(x,y)=9*x+5*y+1` has `i=5` and refutes several former shortest candidates.
Its unit defect is `2*5-1=9`, not zero.

There are 20 chosen operations, on carriers of orders
**9, 13, 17, 29, 37, 41, 49, 53, 73, 89, 97, 101, and 109**. Split primes can
require either square root of -1. The 9- and 49-element examples use the
quadratic rings `F3[i]` and `F7[i]`, with `i²=-1`; they account for 12 and 10
refutations respectively. **Every chosen countermodel is a quasigroup.**
Thus adding bijectivity assumptions cannot rescue these 144 identities.

[`Equation872AffineOffsets.lean`](../equational_theories/Parastrophes/Equation872AffineOffsets.lean)
contains the exact terms, four-coefficient checks, failures of the image basis,
and quasigroup proofs. Its ordinary kernel checks take about **14 seconds**
for the whole module in this workspace; there is no `native_decide`, external
certificate, or enumeration of all assignments. The two extension-field
examples were also independently checked by exhaustive evaluation in Python.
An earlier 103-element example and four partitioned 10-element examples found
in this same pass became redundant, so they were omitted from the final
concrete Lean certificates. The reusable partitioned affine checker and search
script are retained for further research.

### The two forms that survived the Gaussian family

| Research index (and variable-swapped partner) | Operations | Gaussian constant |
| --- | ---: | --- |
| 24237, 24455 | 26 | `-1+2*i` |
| 35462, 36391 | 28 | `2+i` |

These are **search indices, not canonical equation numbers**. To write the
identities more readably, abbreviate

```
s(t) = t*t
c(t) = t*(s(t)*t)
r(t) = s(c(t))*(t*s(t))
h(t) = t*((t*(t*c(t)))*t).
```

The 26-operation form, with `a=z*x`, is

```
x = (y*(s(a)*(y*(a*(s(a)*(z*r(x))))))) * (z*(z*x)).
```

The 28-operation form, with `a=y*x` and `b=z*x`, is

```
x = (a*(s(a)*(y*(h(b)*(z*(z*x)))))) * (y*(y*x)).
```

There is now a **Lean-proved restricted converse for both forms**. Within the
family `D(x,y)=(1-i)*x+i*y+1`, each characterizes the E872 left image over
**every commutative coefficient ring**, finite or infinite. Indeed,
`c(x)=x+2+2*i`, the unit identity has defect `2*i-1`, and the cross identity has
defect `5*i`. The image condition is exactly `2*i=1`; every row has the explicit
inverse `y ↦ -i*(y-(1-i)*x-1)`. The two remaining constants are associates:
`2+i=-i*(2*i-1)`. Consequently either remaining candidate holds exactly when
the image condition does. These are theorems `candidates26_iff` and
`candidates28_iff` in
[`Equation872GaussianAffine.lean`](../equational_theories/Parastrophes/Equation872GaussianAffine.lean).
This proves that further searches **within this particular family** cannot
refute them; it does not establish their unrestricted converses.

### An exceptional cubic field eliminates the 28-operation form

A final coefficient-ideal calculation reveals an extra component in
**characteristic three**. Take

```
F27 = F3[q]/(q³+q²+q-1),
D(x,y) = (q²-1)*x + q*y.
```

Both 28-operation candidates hold, but the image basis fails. The cubic has
no root in F3, so this is a field; both scalar coefficients are nonzero.
This is a **27-element quasigroup counterexample**, removing indices 35462
and 36391. The cubic field requires three coordinates; the earlier unrestricted
matrix searches over F3 had used only two. It lies outside the square-root-of-minus-one family, so it does
not contradict the restricted converses above. The remaining candidates are
**24237 and 24455**, two variable names for the same 26-operation form.

The complete Lean proof is in
[`Equation872CubicCounterexample.lean`](../equational_theories/Parastrophes/Equation872CubicCounterexample.lean).
It implements multiplication by `q²-1` and `q` as 3-by-3 linear operators over
F3. A new generic
[`LinearIdentityCertificate.lean`](../equational_theories/Parastrophes/LinearIdentityCertificate.lean)
proves that **nine basis assignments** suffice for each identity on three
three-dimensional variables. A single assignment disproves the image basis;
explicit inverse matrices establish bijectivity. No 27³ assignment search or
field quotient construction is used in Lean. Python independently checks the
saved 27-by-27 table. The theorem remains a refutation of these particular
identities, not a proof that the image has no single-equation characterization.

The coefficient audit also records why the 26-operation candidate is harder:
its variable constraints imply `p²-p-q³+1=0` and `p*(q²+1)=0` with **integer**
polynomial combination certificates. Modulo these relations its constant
coefficient is exactly the unit-basis constant. This leads to a converse for all commutative-ring affine operations, extending
the Gaussian-family converse. The polynomial certificates were subsequently
formalized in the 2 November pass below; they do not settle the unrestricted
single-equation question.

Additional searches remain evidence only. All scalar coefficients and offsets
were tested over Z/n for `2≤n≤128`. For the last two forms, all pairs of 2-by-2
matrices and all offsets over F3, F5 and F7 produced no counterexamples. Mace4
exhausted six-element quasigroups satisfying either candidate together with a
failure of the unit identity, without finding a model; these exhaustions are
not formalized in Lean and say nothing about failures of the cross identity
when the unit identity holds. Vampire's four-minute quasigroup-to-unit proof
attempts timed out. Neither kind of search settles the general question. Separate unrestricted
Mace4 checks at orders four through six found no counterexample in their short
time limits; only the 28-operation form at order four was fully settled in both
branches. These results predate the 27-element construction and remain
unformalized search evidence.

The exact coefficients, models, proof references, search scopes and the two
remaining candidates are recorded in
[`e872_gaussian_offsets_20261101.json`](../data/parastrophes/e872_gaussian_offsets_20261101.json).
Reproduce the construction and complete accounting with:

```sh
python3 scripts/parastrophe_gaussian_offset_scan.py \
  data/parastrophes/e872_image_basis_followup_20261101.json \
  --output /tmp/e872-gaussian.json
python3 scripts/parastrophe_rewrite_replay.py \
  data/parastrophes/e872_gaussian_offsets_20261101.json \
  --output /tmp/e872-gaussian-replay.json
```

## The final E872 candidate: two broad converses (2026-11-02)

The **26-operation candidate (research index 24237, with renaming 24455) remains
open in general**. This pass proves its converse in two broad classes and finds
no finite counterexample. No single-equation catalogue cell is closed; there
are still 45 finite image-characterization gaps per side.

[`Equation872FinalCandidate.lean`](../equational_theories/Parastrophes/Equation872FinalCandidate.lean)
gives the identity a readable definition and proves that **every actual E872
left image satisfies it, even on infinite carriers**. Write
`c(x)=x*((x*x)*x)` and `r(x)=(c(x)*c(x))*(x*(x*x))`. Every actual image has
`r(x)=x`. If this unary identity can be recovered from the candidate alone,
then the candidate immediately makes every row injective (and hence bijective
on finite carriers). The latter conditional step is also proved in Lean.

### All finite idempotent magmas

**The candidate exactly characterizes the image among finite idempotent
magmas.** Idempotence gives `c(x)=r(x)=x`. Substituting `y=z*x` in the candidate
and simplifying gives

```
x = (z*x)*(z*(z*x)).
```

For each z, the map `a ↦ a*(z*a)` is therefore a left inverse of the row
`x ↦ z*x`. Finiteness reverses the inverse identity, giving
`x=z*(x*(z*x))`. This is precisely the cross-basis law when `c(x)=x`, and the
unit-basis law is automatic. The converse is
`characterizes_idempotent_fin`; the file builds in about five seconds. The
argument genuinely uses finiteness and is not claimed for arbitrary idempotent
infinite magmas.

### All affine operations over commutative rings

**The candidate exactly characterizes the image for every operation
`D(x,y)=p*x+q*y+s` over any commutative ring**, finite or infinite. This includes
all characteristics, nilpotents, zero divisors, and the zero ring; no field or
invertibility assumption is imposed in advance. This extends the previous
square-root-of-minus-one family to arbitrary coefficients.

The new converse is
[`Equation872FinalAffine.characterizes_affine`](../equational_theories/Parastrophes/Equation872FinalAffine.lean).
Computing the candidate's four coefficients, and taking explicit polynomial
combinations with integer coefficients, gives

```
p²-p-q³+1 = 0,
p*(q²+1) = 0,
s*(p*q²+q²+q+1) = 0.
```

These relations imply both image-basis laws. The first two also give
`q*(q⁴+q²-q)=1`, so the original multiplication can be recovered explicitly as

```
M(x,y) = (q⁴+q²-q)*(y-p*x-s).
```

The proof checks both inverse identities and then E872. Thus it needs no
finiteness assumption. The integer polynomial certificates, including the
longer combinations that extract the two variable constraints, are checked by
Lean's ring tactics. The module builds in about ten seconds. No `sorry`,
`native_decide`, or trusted external algebra computation is used.

### Bounded searches and their limits

The SAT encoding exhausts **all possible counterexamples at orders 2, 3, 4,
and 5**. For each order it treats two cases: a failure of the unit law, or the
unit law holding while the cross law fails. At order five the two Glucose runs
took roughly 233 and 131 seconds. These UNSAT results are **not Lean proofs**;
only the two general converses above and the auxiliary lemmas are formalized.
Unrestricted order-six CaDiCaL runs timed out after ten minutes per case.
Three-minute searches imposing row bijectivity, or specifying a row collision,
also timed out. Order six remains the smallest unchecked order for this
candidate.

The finite-model searches are reproducible with
[`parastrophe_e872_candidate_sat.py`](../scripts/parastrophe_e872_candidate_sat.py).
The encoder's constraints are checked against direct evaluation on every
two-element table and all 256 operations preserving two two-element blocks
with bijective rows. Positive solver outputs are independently validated as
multiplication tables before they are saved. A timeout is always distinct from
UNSAT in the research records.

Further completed searches found no counterexamples in:

- All linear/affine operations on F2³, allowing noncommuting coefficient
  matrices and all offsets: 262,144 coefficient pairs.
- All pairs of upper triangular 3-by-3 matrices over F3 and all offsets:
  531,441 coefficient pairs.
- Row-bijective operations preserving the right input's block, with arbitrary
  fibre permutations: two blocks of size three, two of size four, and three
  of size three. Both basis-failure cases were exhausted in each family.
- Operations `alpha(x^k)*beta(y^l)*c` on Q8, D8, S3, A4, and D12, using all
  automorphisms, powers, and offsets. These include noncommutative and
  non-idempotent constructions.

Consequently a finite counterexample must be non-idempotent and cannot be an
affine operation over a commutative ring. The unrestricted question is still
whether the single candidate forces the exact two-equation basis, including
row bijectivity. The complete record is
[`e872_final_candidate_20261102.json`](../data/parastrophes/e872_final_candidate_20261102.json).
All new Lean modules pass the parastrophe build and an axiom audit using only
`propext`, `Classical.choice`, and `Quot.sound`. No unconditional
characterization attribute is attached to these restricted converses.

## Different image questions: E910 and E714 (2026-11-02)

This pass sets E872 aside. It adds one exact **partial-source** correspondence
and refutes a previously unresolved E714 candidate. It does **not** settle
E910's or E714's unrestricted single-equation image question: the finite
inventory remains **45 image gaps per side and 4618 fully settled rows**.

For E910, left division gives a particularly short description:

> The image consists exactly of **E427 models with bijective rows**, on
> finite or arbitrary carriers.

Here E427 is `x = x*(y*(x*(x*y)))`. If M satisfies E910 and D is its left
division, rotating the multiplication constraints gives

```
D(x, D(y, D(y,x))) = M(y,y).
```

One more division gives E427. Conversely, cancelling an instance of E427
recovers E910 for the inverse operation. In the reverse direction this is a
genuine recorded characterization: **among E427 models admitting left
division, their divisions are exactly the E910 models**. It is registered as
`Catalogue.left_characterizes427_all_partial`, exported, and automatically
supplies the reverse FO-structural arrows. It does not assert that arbitrary
E427 models have division, or that all E427 models are in E910's image.

The same proof recovers the original square map by the three-operation term
`c(x)=x*(x*(x*x))`, in the division operation. It proves `c(c(x))=x*x`.
When the original magma is idempotent, multiplication is recovered by the
two-operation term `D(y,D(y,x))`. In general, however, even E427 together with
the displayed cross identity and square-map identity does not force
cancellation. The following three-element table satisfies all three and
has a collision in row 0:

```
2 2 0
2 2 1
0 0 2
```

These statements and the table are kernel checked in
[`Equation910Image.lean`](../equational_theories/Parastrophes/Equation910Image.lean).
A separate inverse-term search refuted seven proposed recovery terms of
lengths 5–17 using E910 models of orders 4–9. After adding all seven tables,
the search exhausted 119,380 term-value signatures through seven operations;
its inverse lookup at the root also excludes **every recovery term through
eight operations**. This is a bounded Python result, not a Lean theorem and
not a proof that no longer recovery term exists. Every retained countermodel
and failed evaluation was checked independently of Mace4.

For E714, put

```
F_y(x) = y*(x*(x*(x*y)))
G_z(x) = (z*x)*((z*x)*((z*x)*z)).
```

Its actual left-division image satisfies `F_y(x)=G_z(x)=x`. The proposed
22-operation compression `F_y(G_z(x))=x` already forces bijective rows, but
allows the two maps to be nonidentity inverses. A small algebraic example
realizes precisely that obstruction. In the nine-element ring
`R=F₃[ε]/(ε²)`, define `x*y=(-1+ε)(x+y)+1`. This operation is a commutative
quasigroup; `F_y(x)=x+2ε` and `G_z(x)=x+ε`. Their composition is the identity,
but E464 fails. Thus this refutes the candidate even in a highly restricted
finite class. In coordinates the operation is
`(a,b)*(c,d)=(-a-c+1,a+c-b-d)`. Lean checks the two coordinates symbolically,
without enumerating the 729 three-variable assignments, in
[`Equation714ImageCandidate.lean`](../equational_theories/Parastrophes/Equation714ImageCandidate.lean).
This resolves the candidate labelled `joinedPowerCandidates[3]` in the
23 October record; it is not a negative answer to all possible
single-equation characterizations.

The full parastrophe build and export audit pass. Both modules use only the
usual Lean axioms, with no sorries or native checking. Search inputs, failed
terms, finite tables, and reproduction commands are retained in
[`e910_e714_images_20261102.json`](../data/parastrophes/e910_e714_images_20261102.json).

## Exporting, previewing and publishing

The normal `scripts/build_website_data.py` pipeline builds the new modules, runs
the attribute rejection checks, exports the records and checked transfer rules,
runs the JavaScript tests, and includes `research/data/parastrophes.json` in the
version-2 deployment bundle. Proof links use the same source commit as the other
research data. No Lean work is added to GitHub Pages deployment.

For a small local preview during development:

```sh
lake build equational_theories.Parastrophes
lake env lean scripts/export_parastrophes.lean
python3 scripts/generate_parastrophe_site.py --local
node --test scripts/test_research_parastrophes.mjs
```

The export defaults to `/tmp/website-parastrophes.json`; `WEBSITE_PARASTROPHES`
overrides it. The Python wrapper's `--input` and `--output` arguments control
its input and website destination. `--local` explicitly marks uncommitted
sources and displays file/declaration locations without invented commit links.
Publication refuses local data or a source-commit mismatch.

The page supports `?eq=543`, `?flavour=fin`, `?quasigroup=yes`, and
`?unproved=1`, and `?representatives=1`. The representative filter uses ordinary
implication classes in the selected carrier scope; a search for any member finds
its representative. Its unproved filter retains laws with at least one relevant field
without a complete Lean proof; non-quasigroup laws are complete for this purpose.
An equation's focused panel compares both carrier settings at once. The same
panel appears in the Equation Explorer.

Version-1 bundles still restore and serve the existing explorers. The new page
explicitly reports missing parastrophe data until the next refresh, rather than
presenting missing data as mathematical unknowns. Restore removes any stale
parastrophe asset left over from a different bundle.

## One-sided schema (16 October 2026)

The Lean attribute parser accepts `SideQuasigroupLaw` and its negation and emits
`kind: "sideQuasigroup"` with an obligatory `side: "left" | "right"`. The existing
`kind: "quasigroup", side: null` is retained for the aggregate property. Scope,
polarity, proof status, theorem location, target identity and concrete term remain
extracted from theorem types. Both result and conjecture attributes support the
new predicate; unchecked claims never enter proved closure.

The JSON schema is **version 2**, because the mathematical meaning of `InImage`
and `Characterizes` has changed. Regenerate the Lean export and site JSON; do not
reinterpret a version-1 image claim with the new semantics. All existing exact
characterizations and the E543 negative were rechecked under the broader image
definition. No old negative was promoted to a one-sided negative without checking
its actual witness/proof.

Twenty-five existing counterexample proofs now also register the specific side
that fails. `OneSided.lean` adds the simple E16 involution and E4 projection cases,
and further finite left-division solutions that were hidden by aggregate
non-quasigroup status. The generic free-model and finite-iteration proofs in
`Uniform.lean` now need only one family of bijective translations. The viewer,
Equation Explorer panel, filters, completion metric and inventory script use the
same side-aware closure. Source references include all extra premises, including
the source-side assumption when reversing an exact characterization.

The initial one-sided export contained **203 checked results** and **36 supporting theorems**
(closure rules and composition identities). No conjectural records or new axioms
were added. Twenty-three new finite counterexample tables, of orders 2–6, were
checked by ordinary kernel reduction. They include the failed side explicitly;
search failures at other orders are not used as evidence.

| Scope | Left bijective: yes | Left: no | Left: unknown | All applicable fields settled |
|---|---:|---:|---:|---:|
| Arbitrary carriers | 1840 | 2598 | 256 | 4172 / 4694 |
| Finite carriers | 2106 | 2584 | 4 | 4158 / 4694 |

Right-side counts are identical by duality. The complete finite bijectivity gaps
are **left E1518, E2697, E2700, E2910**, and **right E677, E870, E907, E2054**.
E1518 already has a counterexample to right bijectivity, so its left-side gap was
invisible under the old completion rule. E2054 is its dual. The other six gaps
are the previously identified two-sided quasigroup questions.

New short positive arguments include E1525's finite left bijectivity: the maps
`L_(y*y)`, `L_y`, and squaring compose to the identity, so each is a permutation
on a finite carrier. E1793 has uniform left division even on infinite carriers:
`L_(u*v)` and `L_(v*u)` are inverses, and every element is a product. The displayed
term is `(((x*x)*x)*(x*x))*y`. E4 and E16 also now have exact one-sided image
characterizations visible through the general self-division rule.

Small-model probes found no left-nonbijective E1518 model through orders 2–5;
order-6 and order-7 probes timed out at ten seconds each. These are search notes,
not Lean exclusions or evidence for universal bijectivity. There are still many
independent exact-image and finite-uniform-term questions, even when bijectivity
is settled. The lower completed-row count compared with the historical audit
reflects those newly visible questions, not lost proofs.

## Further discovery pass (16 October 2026)

At the end of this pass the catalogue contained **238 checked result declarations**, an increase
of 35 over the initial one-sided pass. All new records have complete Lean proofs.

### Reverse chains of left translations

`TranslationChains.lean` proves that

```
L_a1 (L_a2 (... (L_ak x))) = y
```

is equivalent to applying inverse translations in reverse order to y to recover
x. In the left-division operation these inverse translations are simply its own
left translations. If the transformed equation guarantees the relevant division,
this gives an **exact** characterization of the image, not just a one-way law.
`characterizes_of_division` checks both semantic transfers and constructs the
inverse operation; it does not assume right bijectivity.

New left-division characterizations (with dual right-division results automatic):

| Scope | Source | Exact image |
|---|---|---|
| Arbitrary carriers | E75, E513, E528, E562 | Each is its own image |
| Finite carriers | E65, E68, E466, E469, E474, E501 | Each is its own image |
| Finite carriers | E464 and E511 | Each is the other's image |
| Finite carriers | E476 and E503 | Each is the other's image |

The hypotheses on carrier scope matter: a reversed identity alone need not
force bijective left translations on infinite carriers.

### Additional bijectivity results

* E75 and E513 have left translations of exponent three and four, respectively,
  so their inverse translations are fixed positive powers on **all** carriers.
* E127 gives `L_y L_(y*y) = id`. Applying the law again to `y*y` gives a right
  inverse for `L_(y*y)`, forcing the original inverse pair to work both ways.
  Its uniform left division is `(x*x)*y`, with no finiteness assumption.
* E510's square map commutes with every left translation:
  `x*(y*y) = (x*y)*(x*y)`. This identity is extracted from the existing checked
  proof in `Definability/Parastrophic.lean`. Together with E510 it proves that
  `x*(x*(y*y))` is a uniform left division on **all** carriers.
* Existing infinite countermodels refute left bijectivity for E511, E917,
  E1117, E1289, E1323 and E1491. For E511, E1289 and E1323, left cancellation
  would force the missing cyclic rotation. E1491 already gives injectivity;
  surjectivity would imply E65, contradicting the saved Obelix model.
* `Equation1518.lean` records a collision in the existing E1518 free-group
  model. Thus its arbitrary-carrier left-bijectivity question is negative.
  Its **finite** left-bijectivity question remains open.

### Finite division images that admit no defining identity

`FiniteGroupImage.lean` supplies a new general obstruction. If the source law
holds in every finite cyclic subtraction magma, its right-division image contains
every finite cyclic addition group. Any identity shared by these groups holds
in natural-number addition: for any proposed evaluation, take the modulus larger
than the two natural-number values. Natural addition maps onto the two-element
join semilattice by testing whether a number is positive, so the identity holds
there too. But that semilattice has a constant right translation and cannot be
in any right-division image. This contradicts an exact characterization.

The argument rules out **any** single magma identity, of unbounded finite length,
not just an entry in the catalogue. It needs no finite-model search certificate.
It applies to E543, E917, E978, E1113, E1117, E1152, E1658, E1670, E1673,
E1876, E2444 and E2447. Ordinary equivalence and duality propagate the records.
In particular, E543's right-division image has no single-equation characterization
**even on finite carriers**, settling the question left open by the older
natural-number submagma argument.

### Counts after closure

| Measure | Before this pass | After this pass |
|---|---:|---:|
| Arbitrary-carrier quasigroup gaps | 44 | 32 |
| Arbitrary-carrier left-bijectivity gaps | 256 | 128 |
| Arbitrary-carrier right-bijectivity gaps | 256 | 128 |
| Finite left-image characterization gaps, where applicable | 324 | 175 |
| Finite right-image characterization gaps, where applicable | 324 | 175 |
| Fully settled arbitrary-carrier rows | 4172 | 4192 |
| Fully settled finite rows | 4158 | 4424 |

The finite bijectivity gaps remain the same four on each side. These counts use
the side-aware version-2 applicability rules throughout; no change of counting
convention is responsible for the improvement. Reproduce them with
`node scripts/parastrophe_inventory.mjs --json`.


## Third discovery pass (16 October 2026)

At the end of the third pass the export contained **259 checked result declarations**. That pass added
21 declarations and upgrades two existing finite characterizations to arbitrary
carriers. All results are proved in Lean, with no conjectural records or added
axioms. Dual right-side statements and ordinary-equivalence transfers are
included automatically by the existing checked closure rules.

### Fixed inverse terms from functional factorizations

`RotatedDivisionTerms.lean` proves the elementary finite-set principle
`f ∘ g = id → g ∘ f = id`. The factors can be arbitrary unary polynomials, not
just individual translations. Rotating a factorization until a chosen
translation is last gives a fixed term for its inverse. For example E1525 says
`L_(y*y) ∘ L_y ∘ S = id`, where `S(x) = x*x`. Rotation gives
`S ∘ L_(y*y) ∘ L_y = id`, so left division is
`x \ y = ((x*x)*y)*((x*x)*y)`. Its length does not depend on the model's order.

This supplies uniform finite left-division terms for E1525, E2291, E2294,
E2301, E2328, E2497, E2504, E2531 and E2903. E1586 inherits the E1525 term.
E2734 requires one further step: the same rotation constructs the square root
`r(x) = ((x*x)*x)*x`, with `r(x)*r(x) = x`. Its left division is then
`(y*r(x))*(y*r(x))`. In E464, three successive left divisions recover right
division, settling the corresponding left term for its dual E3103.

Among laws whose relevant finite translations are already proved bijective,
the remaining **uniform left-term gaps are E1516, E2091 and E3140**. The right
list is obtained by duality. There are four additional unknown term cells on
each side because the relevant finite bijectivity itself is unresolved.

### Exact self-images

* E68 and E469 now have their existing self-characterizations on **arbitrary**
  carriers. Existing ordinary implications supply E75 and E513 respectively,
  hence bijectivity; the reversed-chain proofs need no finiteness. Their large
  ordinary-equivalence classes account for most of the newly completed rows.
* E138 has an exact left-division self-image on arbitrary carriers. It says
  `L_y ∘ L_(z*y) = id`. If `u = z \ y`, then `z*u = y`; substituting u for y in
  the original law and reversing the two translations gives the same E138 law
  for division. The source law itself supplies the required left bijectivity.
* E510 also has an exact left-division self-image on arbitrary carriers. Its
  square map commutes with each left translation. Under division the new square
  map is the inverse of the old one, as are the translations, so the defining
  relation `L_y³ ∘ S = id` persists.

The last two arguments are in `TranslationFibres.lean`. They verify both
semantic directions and do not assume the unused right division exists.

### Existing countermodels with stronger conclusions

`CancellationObstructions.lean` replaces the finite-permutation steps in existing
implication proofs by explicit cancellation hypotheses. The established infinite
countermodels then refute those hypotheses:

* E65, E476, E504, E713 and E1112 need not be **left quasigroups** on arbitrary
  carriers. Their left translations remain proved bijective on finite carriers.
* E1076, E1110 and E1276 need not be **two-sided quasigroups** on arbitrary
  carriers. These arguments use both kinds of cancellation and do not identify
  a particular side that fails; both side-specific infinite questions remain
  open. Their finite quasigroup results are unaffected.

No new model-search certificate is needed for these obstructions.

### Counts after closure

| Measure | Before this pass | After this pass |
|---|---:|---:|
| Arbitrary-carrier quasigroup gaps | 32 | 26 |
| Arbitrary-carrier left-bijectivity gaps | 128 | 123 |
| Arbitrary-carrier right-bijectivity gaps | 128 | 123 |
| Arbitrary-carrier image-characterization gaps, per side where applicable | 276 | 160 |
| Finite image-characterization gaps, per side where applicable | 175 | 167 |
| Finite uniform-term gaps, per side where applicable | 19 | 7 |
| Fully settled arbitrary-carrier rows | 4192 | 4424 |
| Fully settled finite rows | 4424 | 4440 |

These are numbered-law counts using the same version-2 applicability rules,
including ordinary-equivalence and duality closure. The finite quasigroup and
one-sided bijectivity gaps are unchanged. The parastrophe Lean build, attribute
checks and website regression tests pass; the local website JSON has been
regenerated. Publishing still requires refreshing the deployment bundle.


## Fourth discovery pass (16 October 2026)

The current export contains **268 checked result declarations**. Nine new
records finish the remaining finite uniform-term gaps with known bijectivity,
add exact division-image characterizations, and add image and bijectivity
obstructions. All are complete Lean proofs.

### Uniform terms for every established finite division

`SquareRoots.lean` provides the final constructions. For E467, writing `d` for
its known left division, evaluating `d(x,x*x) = x` gives
`(x*x)*((x*x)*(x*x)) = x`. Thus the unary term `T(u) = u*(u*u)` inverts squaring.
If `c = x*y`, the law and cancellation give `c*(c*(x*x)) = y`; applying left
division twice and then T recovers x. This supplies right division in E467 and
left division in its dual E3140.

For E1516, put `q(x) = x*(x*x)` and `r(x) = q(x)*(q(x)*x)`. Then r is a square
root on every finite model. Here is the calculation behind the Lean proof.
Writing `S(x) = x*x`, rotate the law to obtain

```
(S(a)*z) * ((S(a)*z)*a) = z.
```

Use this at `(a,z) = (y,S(y))`, and compare with the original diagonal law at
`S(y)`. Cancellation gives `S(S(y))*y = S(y)*S(S(y)) = q(S(y))`.
The rotated law at `(S(y),y)` therefore gives `r(S(y)) = y`. Finiteness turns
this into `S(r(x)) = x`. Consequently the fixed division terms are

```
x \ y = y * (y * r(x))
x / y = S(x \ (x \ y)).
```

The apparent divisions in the second formula are expanded using the first;
the exported witness is a parameter-free multiplication term. No exponent
or term length depends on the order of the model.

**Within this catalogue, every proved finite left/right bijectivity property
now has a proved uniform term.** The four remaining unknown uniform-term cells
on each side are precisely the four unknown bijectivity cells. This is an
observation about the catalogue, not a general theorem equating the two
properties for arbitrary identities. E1516 and its dual still have infinite
countermodels, so these finite terms do not upgrade their arbitrary-carrier
bijectivity claims.

### More exact images

`ExactImages.lean` proves on arbitrary carriers:

* **E692 is its own left-division image.** An intermediate identity is
  `x \ (y \ z) = (z*y)*x`.
* **E898 and E1368 are exactly left-parastrophic.** For E898 one derives
  `(x \ y) \ z = (z*x)*y`; for E1368 the corresponding expression is
  `(y*z)*x`. The source laws and the two inverse identities give both transfers.

Short equational searches found the transfers. Their complete proofs are
replayed in Lean using `superpose`, and the existing bijectivity theorems supply
the converse's division operation. The external solver is not trusted and no
external proof certificate is required to build these modules. Duality and
ordinary equivalence also fill the corresponding right-image fields.

### More negative characterizations

`WeightedImageObstructions.lean` generalizes the cyclic-group obstruction:
if a source contains `x*y = y-k*x` over every finite cyclic group, with a fixed
positive integer k, its left image contains all operations `k*x+y`. Any identity
of these finite reductions holds on natural numbers: choose a modulus larger
than its two evaluated values. The map testing whether a natural number is
positive takes `k*x+y` onto Boolean join. Thus the identity holds in the
two-element join semilattice, whose translations are not bijective and which
cannot belong to the image.

This proves **no single equation characterizes the finite left images of E127
(k=2) or E716 (k=3)**. It excludes identities of arbitrary finite length, not
just the numbered catalogue. The cyclic subtraction argument also proves that
**E870's finite right image has no single-equation characterization**. E870's
finite right-bijectivity question remains open: the negative image result does
not assert that some source model lacks that division.

The existing E1117 integer model `x*y = 2*x - floor(y/2)` also supplies a new
right-bijectivity negative. Its zero column is `x ↦ 2*x` and misses 1. Its row
collisions had already been recorded. Ordinary implication and duality propagate
the new failure to E1113, E2534 and E2538.

### Counts after closure

| Measure | Before this pass | After this pass |
|---|---:|---:|
| Arbitrary-carrier quasigroup gaps | 26 | 26 |
| Arbitrary-carrier bijectivity gaps, per side | 123 | 121 |
| Arbitrary-carrier image-characterization gaps, per side where applicable | 160 | 140 |
| Finite image-characterization gaps, per side where applicable | 167 | 147 |
| Finite uniform-term gaps, per side where applicable | 7 | 4 |
| Finite uniform-term gaps with bijectivity already proved, per side | 3 | **0** |
| Fully settled arbitrary-carrier rows | 4424 | 4446 |
| Fully settled finite rows | 4440 | 4464 |

The finite quasigroup gaps remain six numbered laws, and the finite one-sided
gaps remain four per side. A bounded search for an E1518 model without left
bijectivity returned UNSAT at order 6 and timed out at orders 8 and 10; none of
these searches is exported as a Lean result. The positive and negative results
above have passed the parastrophe Lean build and attribute audit. Local website
data has been regenerated; publishing requires refreshing the deployment bundle.

## E467 finite image basis and compression research (2 November 2026)

**No single-equation characterization gap closed in this pass.** The inventory
still has 26 independent finite questions after ordinary equivalence and
duality, or 45 applicable unknown fields on each side.

There is a new exact finite characterization in
[`Equation467ImageBasis.lean`](../equational_theories/Parastrophes/Equation467ImageBasis.lean).
Writing `c(x)=x*(x*x)`, E467's left-division image is precisely the conjunction
of **E411 and E7681**:

```
x = x*(x*(x*(x*x)))
x = y*(y*(c(x)*y)).
```

This pair has nine operations in total. It is registered with
`@[parastrophe_basis]`, so the catalogue can display it as a proved
multi-equation description without answering the one-equation question.
The original multiplication is recovered from division by the four-operation
term `M(x,y)=D(x,D(c(y),x))`.

The proof uses the inverse of the source square map: in finite E467 models,
`x*(x*x)` inverts `x*x`. Reversing the four-step diagonal orbit shows that
the cubic term has the same value in multiplication and division. The square
inverse then reparameterizes the original law, giving E7681. The converse
uses E411 to identify the same cubic term and reverses that calculation.
Both directions are checked in Lean.

The diagonal condition is essential even among finite quasigroups. On the
eight-element field F₂[q]/(q³+q+1), `D(x,y)=x+q*y` satisfies E7681 but fails
E411. Its eight-element table, quasigroup property, and failure to belong to
the E467 image are checked in Lean using ordinary `decide`.

A surviving fourteen-operation compression candidate is also recorded. Put

```
u(x) = x*(x*c(x))
a(y,z) = u(z)*(z*(c(y)*z))
x = y*(a(y,z)*(c(x)*y)).
```

Lean proves that every member of the image satisfies this equation, that any
finite model of it is a quasigroup with bijective c, and that `a(y,z)` is
independent of z. It also proves that the additional assertion `a(x,x)=x`
would give the converse. **Whether the candidate forces that last assertion
is unresolved.** It is not registered as a single-equation characterization.

Three rounds of equational expansion produced 2082 candidates, of which 232
survived the initial prime-field affine checks. Extension-field checks
refuted 78 of those; bounded matrix, nilpotent-ring, and model searches did
not refute the displayed candidate. Vampire and Prover9 did not prove its
converse within the recorded limits. These search outcomes are not proofs.

The broader pass also tested inverse-term candidates for several other finite
families. An eight-element E680 model and a six-element E917 model refute two
short candidates that had survived the initial examples. Candidates for E1110
and E1516 remain unproved; searches for E873, E1276, E1286, E477 and E481 found
no reverse term within their bounds. The checked countermodels and precise
status distinctions are saved in
[`e467_finite_image_basis_20261102.json`](../data/parastrophes/e467_finite_image_basis_20261102.json).


## E467: one finite image-characterization gap closed (2 November 2026)

**E467's finite left-division image now has a single-equation characterization.**
Duality settles E3140's finite right image. This supersedes the open status in
"E467 finite image basis and compression research" above; it does not settle
that section's different `Joined` candidate.

For an operation `*`, put `c(x)=x*(x*x)` and let `v(y)` be six applications of
its y-row to y:

```
v(y) = y*(y*(y*(y*(y*(y*y)))))
x = y*(y*(c(x)*(z*(z*(v(y)*z)))))
```

The second line, with the abbreviations expanded, is **one equation with
fourteen operations and three variables**. Among finite magmas, it is exactly
the conjunction E411 + E7681 previously recorded for this image. The original
multiplication is still recovered by `M(x,y)=D(x,D(y*(y*y),x))`.

The finite part of the proof explains why cancellation can be used without
assuming that the candidate is a quasigroup. The displayed identity first
makes every row and the cubic map c bijective. Its inner bridge is independent
of z. If two indices have the same v-value, they therefore have the same bridge
and the same squared row map. Since v(y) is that squared row applied three times
to y, their indices are equal. Thus v is a permutation. Reparameterizing by v
makes `z*(z*(t*z))` a common map g(t), independent of z. One column is already
known to be bijective from the displayed identity; the common map then makes
all columns bijective. A short calculation with these named maps gives
`v=c`, `g=c⁻¹`, and E411, recovering E7681 as well. Conversely the old basis
reduces v to c and the bridge to y, immediately proving the new identity.

The complete proof is in
[`Equation467SingleImage.lean`](../equational_theories/Parastrophes/Equation467SingleImage.lean),
registered as `Parastrophes.Eq467Image.left_characterizes467_fin_single`.
Vampire found the equational calculation; its steps are replayed as ordinary
Lean equalities. **There are no new axioms, sorries, native checks, or external
certificates.** The new module built in about four seconds on the development
machine, and the full parastrophe target passed.

After ordinary-equivalence and duality closure, the independent finite
image-characterization questions fall **26 → 25**, applicable unknown fields
fall **45 → 44 per side**, and fully settled finite rows rise **4618 → 4620**.
Arbitrary-carrier counts are unchanged. Local website data is refreshed; the
deployment bundle has not been rebuilt in this pass.

## Follow-up: E1516's image and counterexamples to short inverse terms

The fourteen-operation E467 characterization **and** its E411 + E7681
two-equation basis remain registered. The following E1516 result is partial;
it does not close another single-equation field.

For the proposed division operation, write

```
g(x) = x*(x*(x*x))
h(x,y) = y*(y*(x*y)).
```

Among finite **left-quasigroups**, the eight-operation identity
`x = h(x,y)*(x*h(x,z))` characterizes E1516's left-division image.
The intermediate conditions are `h(x,y)=g(x)` and `g(x)*x=g(x)`.
In an actual image, g is the inverse of the original square map. Conversely,
row cancellation extracts the two intermediate conditions from the short
identity and recovers E1516. These implications are proved in
[`Equation1516Image.lean`](../equational_theories/Parastrophes/Equation1516Image.lean).

The left-quasigroup hypothesis cannot be dropped: the table
`[[2,2,1,1],[3,0,3,2],[3,0,2,1],[2,0,0,1]]` satisfies the short identity but
has a collision in its first row. Lean checks both facts. This same table
also refutes all 624 candidates surviving the current affine compression
screen, and all 1284 variants from the subsequent fixed-point rewrite pass.
Those batches are no longer live candidates.

Small affine samples also gave misleading inverse-term guesses for E1110
and E1516. To test them more stringently, extend a known source model B by
a cyclic additive fibre:

```
(i,u)*(j,v) = (B(i,j), a*u+b*v+phi(i,j)) over F_p.
```

The source identity imposes linear equations on the offsets phi. A proposed
inverse term imposes another linear equation; when it is independent, a
nullspace vector supplies a counterexample. In particular, this refutes the
seven-operation E1110 inverse at order 25, the nine-operation E1516 inverse
at order 35, and several proposed unary E1516 square-recovery terms. These
are counterexamples to particular terms, not proofs that no uniform term
exists. The compact construction data is saved in
[`image_cocycle_counterexamples_20261102.json`](../data/parastrophes/image_cocycle_counterexamples_20261102.json).
[`check_parastrophe_cocycle_counterexamples.py`](../scripts/check_parastrophe_cocycle_counterexamples.py)
reconstructs each table, checks its source identity and bijective rows, and
checks the recorded failure. These construction checks are Python research
certificates; they are not exported as Lean results.

## E714: an arbitrary-carrier image question closed (2 November 2026)

**E714's left-division image has a single-equation characterization even on
infinite carriers.** Previously, only its finite characterization was known.
For the proposed division operation, put

```
H(x,y) = x*(x*(x*y))
F(y,x) = y*H(x,y)
G(z,x) = H(z*x,z).
```

The new equation is

```
x = y*F(w,H(G(z,x),y)).
```

With the abbreviations expanded, this has **68 operations and four variables**.
It is exactly equivalent, on arbitrary carriers, to the shorter two-equation
basis `F(y,x)=x` (E464) and `G(z,x)=x`. Both descriptions are registered in
[`Equation714SingleImage.lean`](../equational_theories/Parastrophes/Equation714SingleImage.lean).
The original multiplication is recovered by the three-operation term H(y,x).
The earlier nine-element counterexample concerns the different identity
`F(y,G(z,x))=x`; it does not refute this new equation.

The new identity first forces row bijectivity: the outer y-row is onto, and
every occurrence of x passes through z*x, making the z-row injective. Row
cancellation then shows that F(y,x) is a common bijection a(x), independent of
y, and G(z,x) is another common bijection b(x). Put c=(a∘b)⁻¹. Each row
conjugates the three maps cyclically, a→c→b→a, so its third power commutes
with a. Using H(x,y) as that third power gives both H(a(x),y)=b(H(x,y)) and
H(a(x),y)=H(x,y). Hence b is the identity, and its conjugate a is also the
identity. This recovers the two-equation basis. The Lean proof follows these
named-map calculations directly, with no external certificate or new axiom.

The module builds in about five seconds. The full parastrophe target and its
axiom-audited export pass. After ordinary equivalence and duality, applicable
arbitrary-carrier image gaps fall **6 → 4 per side**. This does not change the
finite count (**44 per side**, or **25 independent finite questions**) or the
number of completely settled equation rows: these equations still have other
open fields. The local website data contains the new single equation and
its shorter basis. The deployment bundle has not been refreshed in this pass.

## Further image research (3 November 2026; ongoing)

**No additional single-equation field has closed in this pass.** The E714
68-operation theorem now includes a proof guide in its Lean module, explaining
the common maps, their conjugation cycle, and the operation count. The module
has been rebuilt successfully.

E1110 provided an important caution about the sample models. Its square map
need not be an automorphism: a **175-element finite counterexample** has now
been constructed. Start with the five-element table in the saved data, extend
it by an additive fibre over F₇, and then extend the resulting 35-element model
by a fibre over F₅. Each extension has the form
`(i,u)*(j,v)=(B(i,j),a*u+b*v+phi(i,j))`. The offsets solve the linear equations
imposed by E1110. The same order-175 model refutes the new 14-operation term
proposed for recovering multiplication from left division. That term had
survived 140 families of extensions of the smaller saved models; iterating
the construction revealed the obstruction. A 13-operation predecessor fails
at order 35, and the proposed division term `c(S(x))=x`, where
`c(x)=x*((x*x)*x)`, fails at order 25.

These are failures of **specified identities**, not proofs that no recovery
term or single-equation characterization exists. Compact construction data
and explicit failing inputs are in
[`image_cocycle_counterexamples_20261103.json`](../data/parastrophes/image_cocycle_counterexamples_20261103.json).
The existing
[`checker`](../scripts/check_parastrophe_cocycle_counterexamples.py) now replays
both November data files, checking the full source tables independently of
the linear-algebra search. The counterexamples are research data, not exported
Lean proofs.

For E872, a new search preserves the subterm `z*x` through which every occurrence
of the recovered variable passes. Every surviving candidate therefore forces
row injectivity syntactically, and row bijectivity on finite carriers. One
48-operation candidate can be written

```
c(x) = x*((x*x)*x)         U(x) = x*c(x)
A(x) = x*(c(c(x))*x)       V(z) = z*((U(z)*z)*z)
B(z,y) = y*(V(z)*(y*z))
x = A(z*x)*(B(z,y)*(z*x)).
```

Every actual finite image satisfies this identity. The converse remains
**unproved**. The finite-table screen retained 42 candidates; dual-number rings
over F₂, F₃, F₅, F₇ and F₁₁ refuted four of them. A separate polynomial-ideal
check over F₁₀₁ showed that the affine instances of all 42 imply the desired
zero-offset affine basis conditions. That check is restricted to characteristic
101; it is not a general converse. The remaining obstacle in the named-map
approach is that cancellation makes the rows indexed by `B(z,y)` independent
of y, without making their indices equal. Images may have repeated rows, so
that distinction cannot be bypassed by assuming column cancellation.

E1518's remaining finite uniform-term question is also under investigation.
Writing S for squaring, a proof of `S³=id` would give a fixed division term
`x\y = y*(S²(x)*y)`. Both this identity and a shorter proposed recovery term
hold on the saved small models; the square identity also survived the central
extension tests above. Neither is proved. Short Prover9 derivations show,
conditionally on bijective rows and squaring, that `S²=id` or `S⁴=id` forces
`S=id`. These conditional calculations have not yet been ported to Lean and
do not settle the arbitrary finite order of S. Further bounded model searches
and proof-search timeouts are not being counted as results.

## E917: a short exact image basis (3 November 2026)

E917's finite left-division image now has a proved **two-equation basis**.
For the division operation `*`, put `c(x)=(x*(x*x))*x`. The basis is

```
x = x*c(x)                  (E1020)
x = y*(c(x)*(x*y)).
```

These have four and six operations, respectively. Original multiplication is
recovered by the five-operation term `M(x,y)=c(y)*(y*x)`. Both directions of
the finite characterization are formalized in
[`Equation917ImageBasis.lean`](../equational_theories/Parastrophes/Equation917ImageBasis.lean),
and `Eq917Image.left917_fin` registers the basis for export. This is a new exact
basis, **not a closure of the single-equation characterization question**.

The recovery formula actually works on arbitrary carriers whenever left
division exists. In multiplication notation set `s=M(x,x)` and choose the
explicit element `b=M(s,M(M(s,s),x))`. E917 and cancellation give `M(b,s)=x`.
The diagonal instance gives `D(x,x)=M(s,s)`; two further instances then give
`M(x,b)=M(s,s)`. Thus `b=D(x,D(x,x))`, and `D(b,x)=s`, identifying the original
square with `c(x)`. Applying the two inverse row operations to E917 gives the
recovery formula. Conversely the basis identifies the same square and reverses
that calculation. Finiteness is needed only to turn the row surjectivity supplied
by the basis into bijectivity. No table certificate or new axiom is used.

The first five proposed compressions are all refuted. Four fail on affine
magmas with constant offsets, at orders 7, 11, and 19. The remaining
28-operation proposal, with `u(x)=x*c(x)`, was

```
x = y*((u(z)*(c(c(x))*(c(x)*z)))*(x*y)).
```

It fails at order 25. Start with a five-element image, attach a fibre F₅, and
use `(i,a)*(j,b)=(B(i,j),2*a+2*b+phi(i,j))`. Solving the candidate's linear
conditions on the offsets gives a quasigroup satisfying both the candidate and
E1020, but violating the second basis identity. The complete multiplication
table was independently checked; the compact construction is saved in
[`e917_image_compression_20261103.json`](../data/parastrophes/e917_image_compression_20261103.json)
and replayed by
[`check_parastrophe_e917_candidates.py`](../scripts/check_parastrophe_e917_candidates.py).
These counterexamples are research data, not Lean proofs. The useful partial
lemmas—that the displayed frame forces finite quasigroups and its bridge is
independent of z—are proved in
[`Equation917SingleCandidate.lean`](../equational_theories/Parastrophes/Equation917SingleCandidate.lean).
A further round of compressions is under investigation; none is registered as
a characterization.

The same pass also rules out the newer five-operation E680 recovery candidate
on `M(x,y)=19*x+4*y` over Z/25Z. It recovers 19 instead of `M(0,1)=4`.
This differs from the older three-operation candidate refuted at order 8.
The modulus-25 construction and failing input are saved alongside the E1110
examples in
[`image_cocycle_counterexamples_20261103.json`](../data/parastrophes/image_cocycle_counterexamples_20261103.json),
and the existing checker verifies it independently. It does not refute the
existence of a different E680 recovery term.

For E872,
[`Equation872RowComparison.lean`](../equational_theories/Parastrophes/Equation872RowComparison.lean)
now proves the row-surjectivity argument for a 24-operation comparison of
`c(c(z))*y` and `(z*z)*y`, and checks a six-element counterexample to its
converse. A 26-operation variant applies a common arbitrary left translation
to both indices and excludes that particular example. Only its forward
implication is proved; even its general finite row-bijectivity claim is still
unproved. Neither candidate is exported as an exact characterization.

Another attempted compression keeps the auxiliary variables independent. Define
`F(x,z)=z*(c(x)*(x*z))`, and put

```
B(x,z,w) = F(z,w)*(c(x)*(x*z))
K(x,z,w) = ((B(x,z,w)*c(x))*(x*x))*x
x = y*(K(x,z,w)*(x*y)).
```

This is a 22-operation, four-variable candidate, now **refuted**. Its forward
implication and the main reduction are formalized in
[`Equation917SplitCandidate.lean`](../equational_theories/Parastrophes/Equation917SplitCandidate.lean).
Finite quasigroup cancellation makes `F(z,w)=g(z)` and `B(x,z,w)=h(x)`.
The maps are permutations, and there is a permutation f with `h=f∘g` and
`m(g(x),y)=f(m(x,y))`. These consequences do not force the image basis, even
with this formula for K. Dropping that formula is also invalid:
`m(x,y)=6*x+2*y+1` on Z/7Z satisfies the common-map relations with
`g(x)=x+4`, `f(x)=x+3`, and `h=id`. Five variants and this warning are saved in
[`e917_split_compression_20261103.json`](../data/parastrophes/e917_split_compression_20261103.json).
The later counterexamples to all five variants are described below. No
additional single-equation characterization field has closed in this pass.

## E481: a finite two-equation image basis (3 November 2026)

E481's left-division image now has a proved finite basis. Write
`c(x)=x*(x*(x*x))`. The two identities are

```
x = x*c(y)                 (E440)
x*(y*x) = z*(y*z)           (E4332).
```

Each has four operation symbols. The first supplies a right identity e; the
second becomes `x*(y*x)=e*y`. The converse includes proving that every finite
model of these identities is a quasigroup. It is not an assertion made only
inside an assumed class of quasigroups.

The finite argument is as follows. Put `f(x)=e*x`. Rotating the crossed
identity gives `(x*y)*f(x)=f(y)`, from which f is an endomorphism. Also
`f(x)=e` forces `x=e`, and this remains true for every iterate of f. Take a
smallest image H of an iterate `f^n`. The map f permutes H, and the crossed
identity makes every column bijective on H. For any a, solve
`b*f^n(a)=e` in H and lift b through `f^n` within H. The singleton fibre over
e then gives `c*a=e` for some c in H. Finally the crossed identity yields
`a=a*e=a*(c*a)=f(c)`. Thus f is onto the whole carrier, and both translations
are bijective. This proof uses no finite-table search and no bounded-period
claim about f.

For forward translation from E481, cancellation makes all source squares a
common e. In division notation `D(x,e)=x`, and E481 becomes
`D(x,D(y,x))=D(e,y)`. Two diagonal substitutions recover e as c(x). These
calculations work on arbitrary carriers whenever the source has left
division. The finite stable-image theorem supplies the bijectivity needed
for the converse, which reverses the translation.

The general lemma is in
[`FiniteCrossedIdentity.lean`](../equational_theories/Parastrophes/FiniteCrossedIdentity.lean);
the translation, exact converse, and exported `Eq481Image.left481_fin`
record are in
[`Equation481ImageBasis.lean`](../equational_theories/Parastrophes/Equation481ImageBasis.lean).
This is a checked multi-equation description. **Whether one equation suffices
is still open.** In particular, it must not be counted as a newly closed
single-equation field.

The presentation also makes recovery-term searches smaller: if
`f(x)=e*x`, then original multiplication is `M(x,y)=f⁻¹(y)*x`. A search for
that unary inverse produced ten- and fourteen-operation candidates on the
initial samples. Mace4 refuted them at orders 9 and 13, respectively, using
the short right-unital crossed presentation. The tables were independently
checked against both basis identities and E481 after reversing division.
They are saved in
[`e481_image_basis_20261103.json`](../data/parastrophes/e481_image_basis_20261103.json)
as research counterexamples, not Lean-certified negative results about
arbitrary recovery terms. Neither candidate should be reused as a theorem.

The E917 compression investigation also now has checked fixed-point and
iterate lemmas: a fixed point of either common permutation forces both to
be the identity; any power fixing one point is the identity everywhere.
Those lemmas remain available, but the counterexamples below rule out finishing
these particular candidates. An audit of compositions of the six quasigroup parastrophes found no
previously unrecorded solved image field; it did identify the finite E464
right-image and E714 right-image questions as equivalent up to opposite.

## E1518: square periods and a broader sample audit (3 November 2026)

**Correction to the earlier square-cube conjecture:** the existing 15-element
table in `Generated/All4x4Tables/Refutation939.lean` has square cycles of lengths
12 and 3. Thus the earlier proposal `S^3=id`, where `S(x)=x*x`, is false. The
directory name `All4x4Tables` does not bound the sizes of its tables. Those
larger tables must be included when testing proposed division terms. An audit
of source identities and table provenance is saved in
[`repository_image_models_20261103.json`](../data/parastrophes/repository_image_models_20261103.json).
The same audit refutes a new 19-operation E1312 recovery candidate using the
existing order-9 table in `Refutation26.lean`.

For E1518, an additive extension also rules out a universal square period of
12. Given a base B, define `(i,u)*(j,v)=(B(i,j),v+c(i,j))`. The extension
satisfies E1518 whenever
`c(y,x)+c(x,B(y,x))+c(B(y,y),B(x,B(y,x)))=0`. Solving these linear equations
over F3 with total offset one around the seed's twelve-cycle gives a
45-element model with a square cycle of exact length 36. The general extension
argument, the seed, and the exact 36-cycle are proved in
[`Equation1518SquareCycles.lean`](../equational_theories/Parastrophes/Equation1518SquareCycles.lean).
Only the 225 offset equations on the base need checking to prove the enlarged
model's law. Further checked research lifts have orders 135 and 405 and cycles
108 and 324; no general infinite-tower theorem is asserted. Their offsets are
saved in
[`e1518_square_cycles_20261103.json`](../data/parastrophes/e1518_square_cycles_20261103.json).

These examples do not disprove uniform recovery: a recovery term need not be
a power of squaring. A candidate fitted to the enlarged samples used
`H_x(y)=x*(y*x)`, `b(x)=x*(x*S(S(x)))`, and `T(x)=H_x^3(b(x))`.
The proposed eleven-operation inverse-square term is now **refuted** by a
further 1215-element additive extension: at x=0, `x*T(x)=1`, whereas an
inverse square must satisfy `x*T(x)=x`. The offsets and failing input are
saved in the same data file and replayed by
[`check_parastrophe_e1518_extensions.py`](../scripts/check_parastrophe_e1518_extensions.py).
This last extension is checked research data, not a Lean-certified model.

The reduction `H_x(y)=y ↔ S(y)=x` is proved on arbitrary carriers in
[`Equation1518.lean`](../equational_theories/Parastrophes/Equation1518.lean),
and `extension_cross_square` proves the reason that successive extensions
can defeat guesses based on stabilization: once a candidate has the correct
base square-root coordinate, one application of H corrects the new fibre
coordinate. The 135-, 405-, and 1215-element examples successively defeat
`H(b)`, `H^2(b)`, and `H^3(b)`. This does not rule out other forms of term,
and no uniform-recovery field is closed.

## E917: five split compressions ruled out (3 November 2026)

All five remaining split candidates now have counterexamples. For variants
0, 7, 17 and 19, respectively, the affine operations are
`43*x+17*y+1` modulo 59, `58*x+4*y+1` modulo 61,
`14*x+24*y+1` modulo 37, and `18*x+72*y+1` modulo 89.
Each satisfies its proposed single identity but fails `x=x*c(x)` at zero.
The original variant 0 is refuted in Lean in
[`Equation917SplitCounterexample.lean`](../equational_theories/Parastrophes/Equation917SplitCounterexample.lean):
the named maps simplify to `c(x)=x+8`, `F(x,z)=x+19`, `B(x,z,w)=x+10`,
and `K(x,z,w)=x+20`. These are short polynomial proofs, with no large table.

Variant 8, with `K=(B*(x*x))*(x*c(x))`, needs an extension field.
Over `F2[b]/(b^3+b+1)`, the operation `(b+1)*x+b*y+1` satisfies the
candidate but gives `0*c(0)=b`, not zero. The same Lean file checks this
eight-element example: first reduce K to a function of x alone (512 triples),
then check only the 64 outer pairs. This also avoids evaluating the whole
long identity on every quadruple.

The discovery used affine coefficient polynomials and resultants to find
exceptional characteristics. In variant 8 the relevant cubic has no root in
F2, but does have one in F8; restricting searches to prime fields missed it.
The exact data and the other three research counterexamples are in
[`e917_split_compression_20261103.json`](../data/parastrophes/e917_split_compression_20261103.json),
all replayed by
[`check_parastrophe_e917_candidates.py`](../scripts/check_parastrophe_e917_candidates.py).
These refute particular proposed characterizations. The exact two-equation
basis remains proved, and whether one equation suffices remains open.

Four longer unit-iteration contexts were also rejected before formalization.
Their 90-, 146-, 166- and 190-operation identities have affine counterexamples
at orders 25, 137, 103 and 7. In the first, `x*y=17*x+2*y+1` modulo 25,
the common map F is already the identity but `u(x)=16*x+5` is not. Thus
eliminating exceptional offsets over fields is insufficient: coefficient
rings with nilpotents must also be checked, as must the other homogeneous
branches. These failures are saved in
[`e917_unit_iteration_candidate_20261103.json`](../data/parastrophes/e917_unit_iteration_candidate_20261103.json)
and replayed by the same checker. No long identity from this batch is a theorem.

## E1719: a finite negative for the right image (3 November 2026)

**New closed field:** the right-division image of finite E1719 models cannot
be characterized by any single magma identity. This also settles the dual
E1888 left-image field. The result quantifies over identities of arbitrary
length and arbitrarily many variables; it is not a bounded candidate search.
The registered theorem is
`Parastrophes.Catalogue.right_noSingleEquation1719_fin` in
[`Equation1719FiniteRightImage.lean`](../equational_theories/Parastrophes/Equation1719FiniteRightImage.lean).

The finite construction works on A = V × V, where V is a finite-dimensional
vector space over F5. Initially turn each pair by
`J(u,v)=(-v,u-v)`. This has order three, and each orbit sums to zero. For
three disjoint orbits represented by `(a,0)`, `(b,0)`, `(c,0)` with
`a+b+c=0`, rearrange the 3×3 array of orbit points: rotate along its rows
instead of its columns. The resulting turn s still satisfies
`s³=id` and `x+s²(x)+s(x)=0`, without enlarging the carrier. Then
`M(x,y)=-s²(x)-y` satisfies E1719, and `R(x,y)=s(-y-x)` is exactly its
right division.

For every ordered pair of basis indices i ≤ j, set
`k=Nat.pair(i,j)+1` and use the triple
`(-e_i-e_j, e_k, e_i+e_j-e_k)` whenever k is in range. The coefficient
patterns over F5 show that all triples are disjoint: their entries are,
respectively, entirely nonpositive, a single positive unit, or have a unique
negative unit at the fresh index k. These simultaneous trades force
`R(e_i,e_j)=e_k`. Thus, for any given term, sufficiently many basis vectors
let all variables evaluate to e₀ while each operation strictly increases
the index. A composite term cannot return e₀.

This refutes every proposed identity with one variable side and one composite
side. If both sides are composite (or the identity is tautological), a
two-element constant magma satisfies it but is not a division image.
Distinct-variable identities fail in a nontrivial constructed image. These
are all possibilities. The generic finite trade and its disjointness proof
are in
[`FiniteTriangleTrades.lean`](../equational_theories/Parastrophes/FiniteTriangleTrades.lean)
and
[`FiniteTriangleBasis.lean`](../equational_theories/Parastrophes/FiniteTriangleBasis.lean).
The proof uses symbolic group calculations and small F5 coefficient checks,
with no model tables, SAT certificates, `sorry`, or `native_decide`.

This argument concerns the **right** image. In this commutative additive
family, left division is the original operation, so a different construction
is needed for E1719's finite left-image question. It is now settled below.

## E1719: the finite left image is also negative (3 November 2026)

**Both finite division-image fields are now closed for E1719 and its dual
E1888.** Neither image can be characterized by a single equation, regardless
of its length or number of variables. The second registered theorem is
`Parastrophes.Catalogue.left_noSingleEquation1719_fin` in
[`Equation1719FiniteLeftImage.lean`](../equational_theories/Parastrophes/Equation1719FiniteLeftImage.lean).
Together with the earlier arbitrary-carrier negatives and the existing
quasigroup and recovery-term theorems, these settle every tracked field of
both equation rows. The finite single-equation gaps drop from 44 to 42 per
side; the number of completely settled finite rows rises from 4620 to 4622.

The new trade works in **any group**, on H × H. Start with
`J(a,b)=(b,a⁻¹b⁻¹)`. For a designated input `x=(a,b)` and chosen element c,
put `y=(c,a⁻¹b⁻¹cb⁻¹)` and `z=(a⁻¹c⁻¹,c⁻¹ba)`. Each of the three rows
`(x,y,z)`, `(Jx,Jy,Jz)` and `(J²x,J²y,J²z)` has first times third times
second equal to 1. Rearranging the three old orbits into these rows preserves
`s³=id` and `x s²(x) s(x)=1`, and makes `s²(x)=z`. Thus
`M(x,y)=(s²(x))⁻¹y⁻¹` satisfies E1719 and its left division, at the designated
input, is `D((a,b),(u,v))=(u⁻¹ca,v⁻¹a⁻¹b⁻¹c)`.

In the free group, protect pairs whose first word starts and ends at generator
0, whose second starts and ends at positive generator indices, and whose last
letters are both positive. Give each protected pair a distinct fresh generator
c, above all indices in its words. The displayed division preserves these
conditions, with first-coordinate length exactly `|u|+1+|a|`. The nine-point
trades are disjoint: each original orbit contains exactly one protected pair;
each new orbit contains none. At its fresh generator, the six new points have
exponent-sum pairs `(1,1)`, `(1,-2)`, `(-2,1)`, `(-1,-1)`, `(-1,2)`, `(2,-1)`.
The larger fresh index separates points from different new trades.

For a given term, select just its finitely many required trades. A finite
permutation representation of the free group preserves all distinctions
between their points and between the term's value and its initial input.
Perform the same trades in that finite group. The resulting finite E1719
left image refutes the proposed isolated-variable identity. As for the right
image, the constant two-element magma excludes the remaining identity shapes.
All steps, including the finite representation, are kernel-checked Lean
proofs, with no `sorry` or `native_decide`.

## Further image research: square translations and candidate refutations (3 November 2026)

**No further single-equation field has closed in this pass.** The finite
counts remain 42 image-characterization gaps per side and 4622 fully settled
rows. The following checked lemmas and research counterexamples must not be
counted as positive or negative answers to the remaining single-equation
questions.

For E873, left division D recovers the source square by the two-operation term
`c(x)=(x*x)*x`. Indeed, if S is source squaring, the source law gives
`D(y,x)=M(S(x),S(y))`, hence `D(x,x)=S²(x)`; a second diagonal substitution
gives `c(x)=S(x)`. The two identities
`x*c(x)=x` and `c(x)*(y*x)=c(y)` then characterize the image **among left
quasigroups**, even on infinite carriers. Both directions and the recovery
calculation are proved in
[`Equation873DivisionCalculations.lean`](../equational_theories/Parastrophes/Equation873DivisionCalculations.lean).
The same file proves that Boolean `x AND NOT y` satisfies both identities
without belonging to the image. Thus the bijectivity hypothesis cannot simply
be omitted.

There is also a new explicit E115 construction with no fixed bound on square
periods. On `(Z/nZ)²`, for any n>10, start with the three-cycle rotation
`J(a,b)=(-b,a-b)`. Trade the orbits through `(1,0)`, `(4,0)`, and `(-5,0)`
so those three points themselves form an oriented triangle; the other two
rows of their 3-by-3 orbit array are traded at the same time. Write t for the
new turn and put `A(x)=t(x+(1,0))-(1,0)`. Then
`A(0)=(3,0)` and `x+A(x)+A²(x)=-(3,0)`. The operation
`M(x,y)=y+A(y-x)` satisfies E115, with square map
`M(x,x)=x+(3,0)`. Its right division is `R(x,y)=y-A²(x-y)`.

The construction, the source identity, the division formula, and the absence
of a uniform positive square period are proved in
[`Equation115SquareTranslations.lean`](../equational_theories/Parastrophes/Equation115SquareTranslations.lean).
To refute a proposed period k>0, use n=3k+11: k squarings move `(0,0)` to
`(3k,0)`, which is distinct modulo n. This uses nine distinguished points
and symbolic identities, with no large finite table. It excludes a universal
period shortcut; it does **not** exclude other recovery terms.

Eight false term guesses now have saved finite counterexamples:

| Source and division | Rejected proposed term | Countermodel order |
| --- | --- | --- |
| E115 right | 15-operation inverse square | 8 |
| E115 right | 9-operation unary identity | 8 |
| E873 left | 23-operation inverse square | 8 |
| E883 right | 13-operation recovery of multiplication | 8 |
| E477 left | 7-operation recovery of multiplication | 6 |
| E504 left | 13-operation recovery of multiplication | 8 |
| E1279 right | 11-operation recovery of multiplication | 35 |
| E1276 right | 11-operation recovery of multiplication | 18 |

The last two are additive extensions over F5 and F3, respectively; their
offsets solve the source law's linear equations. Their source square maps
also fail to be endomorphisms. These are **research countermodels**, not Lean
certificates: the compact data are in
[`image_candidate_refutations_20261103.json`](../data/parastrophes/image_candidate_refutations_20261103.json),
and every source identity, division table, and failing term evaluation is
independently replayed by
[`check_parastrophe_candidate_refutations.py`](../scripts/check_parastrophe_candidate_refutations.py).

## E917: double-bridge candidates refuted (3 November 2026)

With `c(x)=(x*(x*x))*x`, define

```
U(x)       = x*c(x)
F(x,z)     = z*(c(x)*(x*z))
B1(x,z,w)  = F(z,w)*(c(x)*(x*z))
B2(x,v,t)  = v*(c(x)*(x*F(v,t)))
K(x,z,w,v,t) = (x*(B2(x,v,t)*B1(x,z,w)))*U(x).
```

The 34-operation candidate is `x=y*(K(x,z,w,v,t)*(x*y))`. It has six
independent variables. Its forward implication, finite quasigroup status,
and common-map reduction are proved in
[`Equation917DoubleCandidate.lean`](../equational_theories/Parastrophes/Equation917DoubleCandidate.lean).
The reduction produces bijections g and f with
`F(x,z)=g(x)`, `m(g(x),y)=f(m(x,y))`, `B1=f(g(x))`, and
`B2=f⁻¹(g(x))`. These maps need not be trivial: a counterexample over
ZMod 251 has `g(x)=x+211` and `f(x)=x+37`. In particular, even their justified
bijectivity does not suffice to prove the converse.
The same Lean file completes the converse assuming just one fixed point of g;
one idempotent element of the candidate magma is sufficient. This does not
settle all finite models, since genuine division images can have no idempotents.

This is candidate 5 of 24 placements of `x,U,B1,B2` in the four leaves of
`(A*(B*C))*D`. All 24 placements now have explicit affine refutations.
Twenty are refuted over cyclic coefficient rings; candidate 14 needs F27,
and candidates 4 and 23 are refuted over F121. Their data and precise field
encodings are in
[`e917_double_compression_20261103.json`](../data/parastrophes/e917_double_compression_20261103.json),
replayed by
[`check_parastrophe_e917_double.py`](../scripts/check_parastrophe_e917_double.py).
These checks compare the coefficient vectors of the full six-variable
identity, rather than enumerating all six-tuples. None is an exported
characterization. For candidate 5, the operation `x*y=43x+209y+1` modulo 251
satisfies the entire candidate but has `U(x)=x+211`, contradicting the required
unit law. This refutation is proved symbolically in
[`Equation917DoubleCounterexample.lean`](../equational_theories/Parastrophes/Equation917DoubleCounterexample.lean),
without a multiplication table or exhaustive tuple enumeration. Polynomial
elimination found the prime 251, beyond the earlier bounded scalar checks.

Further candidates were chosen so that their affine obstruction has a unit
resultant, avoiding the exceptional-prime defect. This still does not prove
them: a **50-operation candidate is refuted at order 25** by an additive F5
extension of a five-element seed. Its two independently parameterized bridges
are constant in their auxiliary parameters, yet the image basis fails. The
compact extension data and exact term trees are in
[`e917_normalized_candidates_20261103.json`](../data/parastrophes/e917_normalized_candidates_20261103.json);
[`check_parastrophe_e917_normalized.py`](../scripts/check_parastrophe_e917_normalized.py)
checks the full six-variable identity using bridge independence. This
counterexample is checked research data, not a Lean certificate.

The **46-operation candidate remains unproved**. It uses
`K=(B1(x,z,w)*(B1(x,v,t)*U(x)))*B2(x,r,s)` in the same outer frame,
with eight independent variables. Its forward implication, finite quasigroup
status, common permutations, and converse under a fixed-point hypothesis are
proved in
[`Equation917TripleCandidate.lean`](../equational_theories/Parastrophes/Equation917TripleCandidate.lean).
It survived 730 linear offset-space checks over the ten saved seed tables
and primes through 103. These checks range over additive extensions, not all
finite magmas, so no characterization is exported.

A simpler shortcut is also ruled out in Lean: the crossed identity alone
forces `c(c(x))=x*x` on finite carriers, but need not imply the unit identity.
The operation `x*y=x+3y` modulo 7 satisfies the crossed identity and has
`x*c(x)=0`. The short cancellation proof and symbolic counterexample are in
[`Equation917CrossCalculations.lean`](../equational_theories/Parastrophes/Equation917CrossCalculations.lean).
None of these candidate results changes the catalogue counts.

The reusable group trade is in
[`GroupTriangleTrades.lean`](../equational_theories/Parastrophes/GroupTriangleTrades.lean).
Word endpoints, fresh labels and disjointness are proved in
[`FreeGroupWordCones.lean`](../equational_theories/Parastrophes/FreeGroupWordCones.lean),
[`FreeGroupTradeBlocks.lean`](../equational_theories/Parastrophes/FreeGroupTradeBlocks.lean),
[`FreeGroupTradeLabels.lean`](../equational_theories/Parastrophes/FreeGroupTradeLabels.lean)
and
[`FreeGroupDisjointTrades.lean`](../equational_theories/Parastrophes/FreeGroupDisjointTrades.lean).
The finite representation lemma `injective_on_finset` is in
[`FreeGroupFiniteSeparation.lean`](../equational_theories/Parastrophes/FreeGroupFiniteSeparation.lean).


## E115: the remaining finite image field is negative (3 November 2026)

**Four more finite rows are fully settled: E115, E219, E880, and E2707.**
E115's right-division image cannot be characterized by any single magma
identity, of any length or number of variables. Duality gives E219's left
image, and finite equivalence transfers these to E880 and E2707. The finite
single-equation gaps drop from **42 to 40 per side**; fully settled finite
rows rise from **4622 to 4626**. Arbitrary-carrier counts are unchanged.

The registered result is `Parastrophes.Catalogue.right_noSingleEquation115_fin`
in [`Equation115FiniteImageObstruction.lean`](../equational_theories/Parastrophes/Equation115FiniteImageObstruction.lean).
In fact `boolean_theory` proves more: every identity true in all finite right
images holds in Boolean `NOT x AND y`, which is not a right quasigroup. Thus
**even a collection of ordinary identities** cannot characterize these finite
images. This strengthens a single-equation negative without claiming any new
negative about the independently tracked source-to-division recovery terms.

The construction assigns integer vectors to term values and encodes the two
Boolean values by zero versus positive height. Fresh coordinates preserve the
Boolean multiplication while adding disjoint three-cycles. Any finite term
computation then survives in a finite additive quotient, where nine-point
triangle trades produce an actual E115 model and its right division. The
complete proof and its finite transfer are kernel-checked, with no `sorry`,
`native_decide`, SAT certificates, or large multiplication tables. The three
new combinatorial/transfer modules contain 585 lines; their individual build
times were approximately 5–8 seconds. See the detailed
[proof guide](e115-finite-right-image.md).

The same pass also formalizes the conditional characterization: on arbitrary
carriers, E115's right image is exactly **E221 plus right bijectivity**. Its
recovered square `c(x)=x*(x*x)` is an injective endomorphism, hence a finite
automorphism, and `c(M(x,y))=D(y,x)`. These calculations are in
[`Equation115RightImage.lean`](../equational_theories/Parastrophes/Equation115RightImage.lean).

## E873: a second application of the Boolean obstruction (3 November 2026)

**E873 and its dual E2734 now have completely settled finite rows.** The new
negative concerns E873's left-division image and E2734's right-division image.
Finite image-characterization gaps fall from **40 to 39 per side**, and fully
settled finite rows rise from **4626 to 4628**. Arbitrary-carrier counts are
unchanged. The result is registered as
`Parastrophes.Catalogue.left_noSingleEquation873_fin` in
[`Equation873FiniteImageObstruction.lean`](../equational_theories/Parastrophes/Equation873FiniteImageObstruction.lean).

The E115 proof's constructed magmas do extra work. If A³=id,
`x+A(x)+A²(x)=-s`, and A(0)=s, the opposite source operation
`N(x,y)=x+A(x-y)` satisfies E873. Its square is x+s, and the triangle identity
rewrites the argument in E873 as A²(x-y); the outer A then gives x-y.
This statement holds for the constructed family; it is not a general
implication from E115's dual to E873.

Left division of N is the opposite of the E115 right division. Its finite
term computations therefore simulate Boolean `x AND NOT y`, whose false row
is constant. Every identity true in all finite E873 left images holds in this
non-image, so **no collection of ordinary identities**, and in particular no
single identity of any length, characterizes those finite images. The existing
finite triangle construction is shared through `finite_fragment_common` and
`boolean_theory_from_fragments`; no tables or proof certificates were added.

The full parastrophe build passes. Axiom audits of both E873 and the refactored
E115 theorem report only `propext`, `Classical.choice`, and `Quot.sound`.
The local catalogue export includes the new proved negative and its dual.
See the [shared proof guide](e115-finite-right-image.md) for the construction.

## E917: a sandwich reduction and a complete affine converse (3 November 2026)

**This pass does not close another catalogue row.** The finite image gaps
remain **39 per side**, with **4628 fully settled finite rows**. The following
result is exact for a specified subclass, not for all finite magmas.

For the prospective division operation, put

```
q(x) = (x*(x*x))*x
U(x) = x*q(x)
H(x,y) = q(x)*(x*y)
F(x,y) = y*H(x,y)
G(y,x) = H(y*x,y).
```

The new candidate is `x = y*F(H(G(z,U(x)),y),w)`, with four independent
variables and **782 operations after expansion**. The long expansion is
not needed in the Lean calculations. Its forward implication, finite
quasigroup consequence, and reduction to three permutations are proved in
[`Equation917SandwichCandidate.lean`](../equational_theories/Parastrophes/Equation917SandwichCandidate.lean).
In detail, U is bijective, F(x,y) is independent of y, and G(y,x) is
independent of y. Writing the latter two common maps as a and b gives
`y*a(H(b(U(x)),y))=x`. Proving a=id and U=id would finish the general
converse; this is still open. A tentative permutation-order argument needed
the additional assertion that U commutes with every row, which has not been
derived. It is not used by any of the proved results.

There **is** a complete converse for `x*y=A*x+B*y+d` over every commutative
ring, finite or infinite, proved in
[`Equation917SandwichAffine.lean`](../equational_theories/Parastrophes/Equation917SandwichAffine.lean).
This includes composite characteristic and nilpotents, not just field
examples. The coefficient of x in the candidate supplies an explicit inverse
for the coefficient of U, proving U surjective without finiteness. That is
enough for the general common-map reduction. Parameter independence then
gives A=-B³. The remaining equations
are P(B)=Q(B)=0 and R(B)d=0, where

```
C = (B+1)(B²+1)             K = B³-B+1
P = C K (B⁵-B³+1)          Q = (B-1)(B+1) C K
R = C (B⁷+B⁶-B⁴-2B³+B²+2B+1).
```

The identity P-B³Q=CK and an integral Bezout identity for K and R/C force
Cd=0. Both unwanted translations are multiples of Cd, so they vanish and
the established two-equation image basis follows. No division by an integer
is used, which avoids exceptional-prime gaps. This is a kernel-checked
symbolic proof, with no finite-table certificates and no sorries.

Separate research checks found no counterexample in **340 additive-extension
offset spaces** over the ten saved source seeds, using scalar coefficients
over primes through 43. These spaces also include non-affine examples, but
do not exhaust finite magmas. The candidate tree, exact scope, and a tiny
counterexample to a different, shorter attempted compression are recorded in
[`e917_sandwich_20261103.json`](../data/parastrophes/e917_sandwich_20261103.json).
Run [`check_parastrophe_e917_sandwich.py`](../scripts/check_parastrophe_e917_sandwich.py)
to replay all 340 offset spaces. None of this bounded evidence is exported
as a characterization.

## Further E872 and E917 reductions (3 November 2026; ongoing)

The strengthened E872 row comparison is **refuted**, even on six elements.
With `q(x)=x*((x*x)*x)`, the candidate was

```
x = ((w*(q(q(z))*y))*v) * (q(x)*(((w*((z*z)*y))*v)*x)).
```

It has 28 operations and forces surjective rows on arbitrary carriers, hence
bijective rows on finite carriers. A new six-element table satisfies it but
violates `x=x*q(x)`. Both assertions are checked by the Lean kernel in
[`Equation872DoubleComparison.lean`](../equational_theories/Parastrophes/Equation872DoubleComparison.lean).
The table and search scope are saved in
[`e872_double_comparison_20261103.json`](../data/parastrophes/e872_double_comparison_20261103.json).
An exhaustive check of two-point extensions of the six three-element image
types had missed it: restricting the quotient to an actual image is a real
restriction. The failed candidate must not be reused as a characterization.

For E917, the sandwich candidate now has a shorter, proved permutation
reduction. Its common maps extend to three commuting permutations a,b,c
satisfying

```
x*b(y) = a(x*y)        x*a(y) = c(x*y)
b(x)*c(y) = x*y        a(b(c(U(x)))) = x.
```

These statements, including commutativity, follow by cancellation; no extra
regularity of U is assumed. The proof is in
[`Equation917SandwichPermutations.lean`](../equational_theories/Parastrophes/Equation917SandwichPermutations.lean).
The next conjugation `x*c(y)=b(x*y)` remains unproved. Commutativity of the
three maps alone does not justify it. The catalogue counts are unchanged:
**39 finite image gaps per side and 4628 fully settled finite rows**.

## E917: two first-argument shifts and a shorter row argument

**No additional catalogue row closes in this pass.** A new fifty-operation
candidate has a verified forward implication and finite permutation reduction
in [`Equation917TwoShifts.lean`](../equational_theories/Parastrophes/Equation917TwoShifts.lean).
With q, U, H, F, G as above, write

```
A(x,z,w) = F(z,w)*H(x,z)
B(x,z,w) = z*H(x,F(z,w))
C(x,z,w) = G(w,z)*H(x,z)
K = (B(x,z,w)*(U(x)*A(x,v,t)))*C(x,r,s)
x = y*(K*(x*y)).
```

All eight variables are independent. Finite cancellation forces common
permutations F(x,y)=a(x) and G(y,x)=b(x), with further permutations f,g such
that `a(x)*y=f(x*y)`, `b(x)*y=g(x*y)`, and `x*b(y)=a(x*y)`.
The three parameterized terms become f(a(x)), f⁻¹(a(x)), and g(a(x)).
The pairs (a,f), (a,g), (a,b), (f,b), and (f,g) commute. The remaining pair
(b,g) is **not** assumed to commute; neither a=id nor U=id has been proved.

The useful simplification is independent of the specific formula for K.
Compare its outer identity with `y*(q(x)*(x*y))=a(x)`. This gives
`b(K(x)*z)=q(x)*z` for every z. Apply it at b(z), and use the fact that
every row carries b to a: the two evaluations give ba=ab after a single
surjectivity substitution. Further row comparisons give fb=bf and fg=gf.
[`Equation917FramePermutations.lean`](../equational_theories/Parastrophes/Equation917FramePermutations.lean)
formalizes this short argument; a prover had first found a 99-line derivation.
The lemma works on arbitrary carriers with bijective rows and does not use
the formula for q.

The candidate also survives all **340 additive-offset spaces** over the ten
saved E917 image quotients and the recorded primes through 43. This is a
restricted research check, not an exhaustive search or a converse proof.
The exact tree and scope are in
[`e917_two_shifts_20261103.json`](../data/parastrophes/e917_two_shifts_20261103.json),
replayed by [`check_parastrophe_e917_two_shifts.py`](../scripts/check_parastrophe_e917_two_shifts.py).
Catalogue counts remain **39 finite image gaps per side and 4628 fully settled
finite rows**.

## E917: a quotient reduction and an obstruction to the stable-image shortcut

**The single-equation question remains open.** The following is a conditional
reduction, not an additional catalogue characterization. Assume the crossed
identity `y*(q(x)*(x*y))=x`, and assume a common map w satisfies
`x*U(y)=w(x*y)`, where `q(x)=(x*(x*x))*x` and `U(x)=x*q(x)`.
[`Equation917RegularUnit.lean`](../equational_theories/Parastrophes/Equation917RegularUnit.lean)
proves that U and w are inverse permutations, and that

```
U(x)*y = U(x*y)       U(x)*U(y) = x*y       q(U(x)) = q(x).
```

Consequently the U-orbit relation is a magma congruence. Its quotient satisfies
both the crossed identity and U=id, so it is a genuine finite E917 left-division
image. Every cycle of U has the same length: a period fixing one point fixes
every point, because the columns commute with U and the rows are onto. These
statements are formalized in
[`Equation917UnitQuotient.lean`](../equational_theories/Parastrophes/Equation917UnitQuotient.lean).
Moreover, **an idempotent in the quotient forces U=id upstairs**. Indeed q is
constant on each U-orbit. If `x*x` and x have the same orbit, then
`q(x*x)=q(x)`; using `q(q(x))=x*x` shows that q(x) is an idempotent upstairs.
That supplies a fixed point of U, and hence fixes U everywhere.

Thus any nontrivial regular-unit counterexample must be a uniform cyclic
cover of an **idempotent-free** image. The remaining general exclusion is
unproved. A bounded linear-algebra check found no counterexample in 70 spaces
of central offsets over the ten saved image quotients, with fibre primes
2, 3, 5, 7, 11, 13, and 17; those checks do not prove the general assertion.

One tempting alternative is now ruled out. The stable image of the square
map need not be a submagma, even in a genuine image. The **24-element** example
in
[`Equation917StableImageCounterexample.lean`](../equational_theories/Parastrophes/Equation917StableImageCounterexample.lean)
is an additive extension of the eight-element idempotent model by F3:
`(i,u)*(j,v)=(B(i,j),u+2v+phi(i,j))`. Its square map is idempotent, but two
of its fixed points multiply to a non-fixed point. Lean checks membership
in the division image and this failure. In particular, replacing the quotient
argument by a stable-square-submagma argument would be invalid. No catalogue
counts or proof statuses change in this pass.

## E464: the final arbitrary-carrier bijectivity gap closed (3 November 2026)

**E464 and its dual E3103 need not be quasigroups on infinite carriers.**
The countermodel is idempotent and fails both left and right cancellation.
Every translation is nevertheless surjective, as proved earlier. In particular,
this answers the linked left/right question without changing the positive
finite-carrier results.

[`ManuallyProved/Equation464Idempotent.lean`](../equational_theories/ManuallyProved/Equation464Idempotent.lean)
constructs the model on the free group on countably many generators. Put
`x ◇ y = x f(x⁻¹y)`. The equation
`x = y ◇ (x ◇ (x ◇ (x ◇ y)))` reduces to

```
f(x⁻¹ f(f(f(x)))) = x⁻¹.
```

Start with only three prescribed values: `f(1)=1` and `f(g₁)=f(g₂)=g₃`,
where the generators are distinct. These give idempotence and a collision
in the row indexed by the group identity. For an undefined input d, choose
a fresh generator c and add `d ↦ c`, `h⁻¹c ↦ h⁻¹` whenever `f²(h)=d`,
and `c⁻¹ht ↦ c⁻¹h` whenever also `f²(h⁻¹)=t` in the old partial function.
The new two-step paths have exactly three forms: old paths, `h ↦ c` with
old `f(h)=d`, and `h⁻¹c ↦ t` with old `f²(h)=d` and `f(h⁻¹)=t`.

The key extra invariant excludes the earlier obstruction: **if `f²(h)=d`
and `f(h⁻¹)=d`, then h=1**. Since 1 is already defined, that situation
cannot arise when defining a missing d. Separate collision invariants for
one-step and two-step paths handle the remaining conflicts. Projection onto
the fresh generator distinguishes old elements from the new families, and
Lean proves preservation of every invariant. A greedy increasing chain meets
every input requirement, so its union defines a total f retaining the seed.
The earlier experiments alone did not provide this extension theorem.

The left collision and the existing E464 left/right bijectivity equivalence
also force a right collision in the same model. Both negative catalogue
theorems are registered in
[`Parastrophes/Equation464.lean`](../equational_theories/Parastrophes/Equation464.lean),
and duality propagates them to E3103. The proof uses only Lean's standard
axioms; the three-entry seed is checked by `decide`. There are no `sorry`s,
native checks, or external certificates. The construction module built in
approximately 11 seconds locally; the full parastrophe target also passed.

The refreshed local export has **448 proved records**. Arbitrary-carrier
quasigroup, left-bijectivity, and right-bijectivity status now have **zero
gaps across all 4694 equations**. Fully settled arbitrary-carrier rows rise
**4686 → 4688**. The six remaining open rows concern division-image
characterization: E714, E910, E1120 and their duals E2913, E2737, E2507.
Finite counts remain **4628 fully settled rows**, with **39 image gaps per
side** and the E907/E2700 quasigroup questions still open.

## E481: a lower bound and stronger finite samples (4 November 2026)

**The finite single-equation question remains open.** A complete bounded
Python search now excludes every single identity with at most **ten operation
symbols** for E481's finite left-division image, with no restriction on its
number of variables. This is a research computation, not a Lean theorem.
The existing exact two-equation basis still has eight operations in total;
this bound shows why simply looking for a similarly short single identity
misses the difficulty.

The reduction to a bounded search uses the shape of a proposed identity.
Two composite sides both evaluate to the same element in a constant
two-element magma, so they cannot characterize an image with bijective rows.
For `x=t`, if the leftmost variable of t is x, the left-projection magma
satisfies the identity and again has nonbijective rows. Otherwise set every
other variable to the distinguished right identity e in our actual finite
images. A necessary condition is that a term in x,e, with leftmost leaf e,
evaluates to x for every input in every sample. The search merges terms only
when both their evaluation vectors and their leftmost-leaf tags agree.
It exhausts all sizes through ten, reaching **310,820 tagged signatures**.
Distinct-variable and tautological variable identities are excluded separately
by a nontrivial image and a constant magma, respectively.

The samples include the saved order-9 and order-13 images, all scalar
`x+b*y` examples with `b²=-1` over F5, F13 and F17, and the 625-element
Cartesian-square construction from `CrossInverseLoops.lean` over F5.
The replayer independently verifies bijective rows, the right identity, the
crossed identity, and E481 for each recovered source operation. A proposed
seven-operation identity in the expanded signature with constant e,
`e*(e*((e*((e*(e*x))*x))*x))=x`, is refuted in the last sample at
`x=((0,0),(1,0))`, where it gives `((0,2),(1,2))`.
Reproduce the full bound with
`python3 scripts/parastrophe_e481_short_identity.py --output /tmp/e481-bound.json`.
The recorded output is
[`e481_short_identity_20261104.json`](../data/parastrophes/e481_short_identity_20261104.json).

There is also a stronger source of finite test models. For a cross-inverse
loop Q with unit e and inverse permutation J, an additive central extension

```
(x,u) · (y,v) = (x·y, u+v+c(x,y))
```

remains a cross-inverse loop when `c(e,x)=c(x,e)=0` and
`c(x,y)+c(x·y,Jx)=c(x,Jx)`. Its inverse is
`(x,u) ↦ (Jx,-u-c(x,Jx))`. A solution over F5 extends the 25-element loop
from the earlier construction to a **125-element loop**, extending a
10-cycle of J to a **50-cycle**. The corresponding division magma on Q²
has operation `D((a,b),(c,d))=(a·d,b·Jc)` and has 15,625 elements.
Its right identity and crossed identity place it in E481's finite left image.
It refutes the eight-operation guess `f³(((f³(x))*x)*x)=x`, where `f(x)=e*x`,
which survived the earlier central-extension family. Thus that earlier family
does not suffice for testing arbitrary recovery terms.

Only a 25-by-25 offset matrix is stored; neither a large division table nor
a Lean certificate is introduced. The loop law, inverse automorphism,
bijectivity, exact cycle, and failed term evaluation are independently checked
by `python3 scripts/check_parastrophe_e481_central.py`, using
[`e481_central_extension_20261104.json`](../data/parastrophes/e481_central_extension_20261104.json).
These constructions and bounds do not prove that every possible single
identity fails. Catalogue counts and exported proof statuses are unchanged.

The general construction is now formalized in
[`CrossInverseLoopExtensions.lean`](../equational_theories/Parastrophes/CrossInverseLoopExtensions.lean).
`CIPLoop.extend` proves the central-extension theorem for an arbitrary
abelian coefficient group. `CIPLoop.division_inImage` proves that the
Cartesian-square operation above belongs to E481's finite left image.
The concrete offset matrix and the bounded search remain Python research
checks; they have not been promoted to Lean certificates.

There is also a converse structural description, proved by `normalize` in
the same module. Given a finite magma with right identity e and
`x*(y*x)=e*y`, let f(x)=e*x and define `x·y=x*f⁻¹(y)`. Then · is a
cross-inverse loop, f is its automorphism, and its inverse permutation is
f². The original operation is recovered as `x*y=x·f(y)`. Thus the
remaining single-equation problem can be studied through these loop twists;
the normalization itself does not settle it. The module and the full
parastrophe target build successfully, using only Lean's standard axioms.

## E1516: consolidated samples and a bounded recovery obstruction (4 November 2026)

**No additional image-characterization field closes here.** The repository
sample file does not contain every later counterexample: several central
extensions were saved separately in `image_cocycle_counterexamples_*.json`.
Using only the repository sample file can therefore rediscover an already
refuted recovery term. The new
[`parastrophe_square_term_search.py`](../scripts/parastrophe_square_term_search.py)
loads both sources of examples, adds the scalar affine examples over the
listed primes through 31, and independently checks each source law and each
row's bijectivity before constructing division.

On these 26 samples, of orders up to 387, no unary division term with at most
**twelve operations** recovers the source square. Consequently no uniform
term of that size recovers the entire source multiplication either: setting
all its variables equal would give a forbidden square-recovery term. This
is a bounded Python computation, **not a Lean theorem**, and says nothing
negative about longer terms or arbitrary single-equation characterizations.
The recorded result is
[`e1516_square_term_bound_20261104.json`](../data/parastrophes/e1516_square_term_bound_20261104.json).

The search reaches 200,000 term-value signatures. It completes subterm layers
through eleven operations and partially constructs layer twelve. The stated
twelve-operation bound is nevertheless complete: for every possible root
`D(u,v)`, both children have at most eleven operations, and `v=M(u,target)`
determines the required value vector exactly. The root lookup checks all those
pairs. No completeness is claimed for the partially generated layer or for
thirteen-operation terms. Replay with
`python3 scripts/parastrophe_square_term_search.py 1516`.

## E883 right division: square-map reduction (4 November 2026)

**This is a proved reduction, not another closed catalogue field.** Work with
E2744, the dual of E883, and take left division D; reversing D gives the
original right-division question. The new module
[`Equation883RightImage.lean`](../equational_theories/Parastrophes/Equation883RightImage.lean)
proves that a finite D is in this image exactly when there is a unary map s
satisfying

```
y * (x * (s(x) * y)) = x
x * (s(x) * x) = s(x).
```

The source multiplication is then `M(x,y)=y*(s(y)*x)`, and its square is
exactly s. The first identity makes every row of D surjective; finiteness
gives injectivity, so the proposed M really is its inverse operation. The
second identity identifies its square and lets the E2744 calculation cancel
two inverse pairs. The map s is unique. The forward direction does not use
finiteness. These proofs use no table certificates, `sorry`, or native
evaluation. This is not a magma-equation basis: the auxiliary unary map must
still be eliminated before registering such a result.

Two proposed fifteen-operation terms for s are refuted by extensions of
orders **88** and **28**, respectively. Their complete compact data is in
[`image_cocycle_counterexamples_20261104.json`](../data/parastrophes/image_cocycle_counterexamples_20261104.json).
Each extension has the form
`(i,u)*(j,v)=(B(i,j),a*u+b*v+phi(i,j))`. The first uses an eight-element
base over F11; the second a four-element base over F7. The replay script
checks the full source law, the actual division, and the failed recovery
evaluation. These are checked Python research results, not Lean certificates
or obstructions to every possible term. Replay all saved dates with
`python3 scripts/check_parastrophe_cocycle_counterexamples.py`.

The subsequent seventeen-operation square-recovery candidate is also **refuted**,
now by an order-56 model. Extend the preceding order-28 source by F2 using
`(i,u)*(j,v)=(B(i,j),u+v+phi(i,j))`. Its offsets are stored as 28 bitmasks.
[`Equation883Extensions.lean`](../equational_theories/Parastrophes/Equation883Extensions.lean)
proves the extension construction for arbitrary commutative coefficient rings,
its division formula, both successive source laws, and the failed recovery
evaluation at `((1,0),0)`. The concrete proof checks only 784 offset equations
on the smaller base; the fibre calculations are symbolic. It uses ordinary
kernel checking, with no `sorry` or native evaluation. The seventeen-operation
candidate's saved status is now `refuted`; the two fifteen-operation refutations
above remain Python checks.

Separately, substituting the seventeen-operation term into the crossed identity
alone has a four-element counterexample to the second identity. None of these
counterexamples rules out a longer recovery term or a different single-equation
characterization. Catalogue counts remain unchanged: **39 finite image gaps per
side, 4628 fully settled finite rows**.

## E910: a small extension catches a missed inverse test (4 November 2026)

A thirteen-operation inverse candidate passed all ten saved E910 source models
and the homogeneous scalar affine tests through prime 127. It nevertheless
fails on an **eight-element** source. Take the base operation `i*j=i+j+2`
on Z/4 and extend by F2:

```
(i,u)*(j,v) = (i*j, u+v+phi(i,j)),
phi(i,j) = 1 exactly when i=1 and j is odd.
```

[`Equation910InverseCounterexample.lean`](../equational_theories/Parastrophes/Equation910InverseCounterexample.lean)
checks E910, constructs actual left division, and refutes the candidate
`inverse13` at inputs `(0,0)` and `(1,0)`. Its division also satisfies E427,
as the established image criterion requires. All checks use the kernel;
no solver certificate or admitted theorem is involved. The compact extension
is included in
[`image_cocycle_counterexamples_20261104.json`](../data/parastrophes/image_cocycle_counterexamples_20261104.json)
so future searches can retain this missing test model. This refutes only that
candidate; E910's single-equation image question remains open.

## E481: central towers at arbitrary height (4 November 2026)

The isolated central extensions now extend to a general construction. For
each prime (p>3), there are cross-inverse loops of order (p^{k+1}) whose
inverse permutation has exact order (2p^k). A grading into 𝔽ₚ controls the
extension: choose one nonzero diagonal offset in each nonzero-grade inverse
cycle, then solve the other offsets around multiplication-triple rotations.
The grading makes the alternating cycle sums vanish, so the construction
continues at every height. The proof and its hypotheses are written out in
[`cross-inverse-loop-towers.md`](cross-inverse-loop-towers.md).

The generic extension theorem was already in Lean. The exact period formula
is now also proved in
[`CrossInverseLoopPeriods.lean`](../equational_theories/Parastrophes/CrossInverseLoopPeriods.lean):
the lifted period is the base period times the additive order of the
alternating offset trace. A nonzero prime-field trace therefore multiplies
the period by p. The general orbit-based **existence** of these offsets remains
a pen-and-paper proof, not a Lean theorem.

[`check_cross_inverse_loop_tower.py`](../scripts/check_cross_inverse_loop_tower.py)
constructs and fully checks the loops through order 3125 over F5 (inverse
order 1250) and through order 343 over F7 (inverse order 98). It stores only
a small summary, not large tables. Their Cartesian-square E481 division
images follow from the existing construction theorem. **No new catalogue
row is closed:** growing inverse periods do not by themselves exclude every
inverse term or every single defining equation.

## E477: a short conditional description and its six-element obstruction

[`Equation477Image.lean`](../equational_theories/Parastrophes/Equation477Image.lean)
proves that E477's left-division image, on arbitrary carriers, consists exactly
of the magmas satisfying E411 and E4332 **with bijective rows**:

```
x = x*(x*(x*(x*x)))
x*(y*x) = z*(y*z).
```

Writing c(x)=x*(x*x), the proof identifies c with the source's cubic term
M(x,M(x,x)). The crossed law makes c
an endomorphism. Every x has a local right identity v(x)=x*c(x), and this v(x)
is fixed by c. These deductions do not assume cancellation.

The bijectivity condition **cannot be omitted even for finite magmas**.
Mace4 found a six-element model of both identities whose cubic map is
`[0,0,2,2,4,4]` and whose rows have collisions. Its 36 entries and all the
required checks are now formalized in Lean using ordinary `decide`. This
refutes the proposed two-equation description without the extra condition;
it does not refute every possible single defining equation. No catalogue
characterization attribute is attached, and row counts are unchanged.

A subsequent fifteen-operation inverse candidate is refuted by an order-20
extension, saved in the same data file. That further refutation has been
replayed in Python and is **not yet formalized in Lean**. Neither candidate
should be reused as a proved or surviving inverse formula.

## E872: cancellation built into the candidate (4 November 2026)

**Later update:** the 28-operation candidate displayed below is now refuted
by a six-element magma; see the counterexample section below. The forward
implication, cancellation lemmas, and idempotent converse remain valid.

**No new catalogue row closes in this pass.** A new search starts from the
inverse identity `x=c(z*x)*(z*(z*x))` and protects every occurrence of `z*x`
while substituting the known unit and crossed identities. This ensures that
each candidate itself forces row injectivity. The initial twenty-operation
proposal fails on four elements despite passing the scalar affine tests.
Further tests with two-dimensional matrix operations refute 27 additional
proposals, including several of the shortest ones. These are refutations of
particular formulas, not of the single-equation characterization question.

One surviving twenty-eight-operation proposal is

```
c(x) = x*((x*x)*x)        u(x) = x*c(x)
a(x) = x*((x*x)*u(x))     h(z,y) = y*(c(z)*(u(y)*z))
x = a(z*x)*(h(z,y)*(z*x)).
```

[`Equation872InjectiveCandidate.lean`](../equational_theories/Parastrophes/Equation872InjectiveCandidate.lean)
proves its forward direction, row injectivity, an explicit finite inverse,
and its converse for finite idempotent magmas. More generally, a candidate
with this pattern induces a permutation of the **distinct row maps**. The
module proves the inverse equations on rows without identifying elements
which happen to have the same row. This extra finite reduction is available
for the still-unproved general converse. No characterization attribute is
registered. The module and full parastrophe target build successfully,
with no admitted proofs or native checks.

The candidate survives all tested scalar operations through modulus 31 and
all two-dimensional matrix operations over F2, F3, and F5, including arbitrary
offsets in the matrix tests. Mace4 exhausts its order-five unit-failure search;
the order-six search times out. These are **external research checks only**.
The saved search scope, counterexamples, and remaining formulas are in
[`e872_injective_candidates_20261104.json`](../data/parastrophes/e872_injective_candidates_20261104.json).
Replay the explicit refutations with
`python3 scripts/check_parastrophe_e872_injective_candidates.py`.


## E1516 and E1110: larger recovery searches and new counterexamples (4 November)

**No additional single-equation row closes in this pass.** Enlarging the E1516
square-recovery search to 925,822 value signatures produced a 24-operation
candidate on the existing samples. A seven-element base extended by F19
refutes it at order 133. After adding that example, a 25-operation candidate
appeared; a different seven-element base extended by F7 refutes it at order 49.
Neither formula remains a live candidate.

Both refutations are proved in
[`Equation1516Extensions.lean`](../equational_theories/Parastrophes/Equation1516Extensions.lean).
The module first proves the general affine-extension criterion for E1516
over an arbitrary commutative ring. Each concrete source law then checks only
49 base pairs and 49 offset equations. Actual left division is proved
symbolically, and the failed recovery is checked at one explicit input.
The kernel checks all these proofs; there are no admitted obligations or
native checks. The module built in about seven seconds locally.

For E1110, a seven-operation inverse-square candidate is refuted at order 121.
Its nine-operation successor passes 144 spaces of additive offsets over the
small sampled bases, but a larger-base extension refutes it at order 125.
These two E1110 refutations are **Python research checks, not Lean proofs**.
The four constructions and exact failed terms are saved in
[`image_cocycle_counterexamples_20261104.json`](../data/parastrophes/image_cocycle_counterexamples_20261104.json)
and consumed by the square-term search automatically. The existing independent
replayer checks all four. These examples do not exclude longer recovery terms
or decide whether any division image is characterized by a single equation.

## E1516: the short candidate is exact throughout the finite affine class (4 November)

There is now a proved characterization for all finite affine magmas, although
**no unrestricted single-equation row closes**. On any finite abelian group,
let `x*y=a(x)+b(y)+k`, with arbitrary additive endomorphisms a and b and any
constant k. Neither invertibility nor commutation is assumed. Put
`C(x,y)=y*(y*(x*y))`. Then the eight-operation identity

```
C(x,y)*(x*C(x,z)) = x
```

holds exactly when this magma is the left division of an E1516 model. Moreover,
the identity forces a and b to be bijective **and to commute**. This covers
noncommuting matrix coefficients as potential inputs to the theorem, arbitrary
finite abelian groups (not just vector spaces), and nonzero offsets.

The proof is in
[`Equation1516AffineImage.lean`](../equational_theories/Parastrophes/Equation1516AffineImage.lean).
In the instance y=z=0, expansion shows that all dependence on x passes through
`t=b(a(x))`: the variable part is `a(b(t))+b³(t)+t`. Hence b∘a is injective.
Finiteness gives bijectivity of both coefficients, so the previously proved
converse for magmas with bijective rows applies. Parameter independence then
gives `(1+b)a=-b³`. Since a and b are invertible, 1+b is injective; applying it
to ab and ba proves they agree. These are symbolic group calculations, with no
enumeration, admitted obligations, or native checks.

The existing four-element counterexample to this same identity among general
magmas remains valid; it therefore cannot have an affine presentation of this
kind. The stronger proposed description combining `Common` with the normalized
short identity still has an unresolved converse. E917's 50-operation candidate
also remains open after the additional bounded ATP attempts. E872's
28-operation candidate has subsequently been refuted, as recorded below.
No characterization attribute is attached to the affine theorem.

## E872: the injective 28-operation candidate is refuted (4 November)

The previously highlighted 28-operation candidate does **not** characterize
the finite left-division image. A six-element model satisfies the full
three-variable identity and has bijective rows, but `0*c(0)=4`. Every actual
image satisfies `x*c(x)=x`, so this is a conclusive refutation of that
candidate. It does not decide whether some other single equation works.

The table and proofs are in
[`Equation872InjectiveCounterexample.lean`](../equational_theories/Parastrophes/Equation872InjectiveCounterexample.lean).
Lean checks the 216 assignments directly; the module builds in about six
seconds. There is no SAT certificate or native check. Rows 0, 3, and 4
coincide, illustrating why the earlier results carefully distinguish equality
of row maps from equality of their indices. The auxiliary map U fixes every
point except 0, which it sends to 4.

CaDiCaL found the model in about 91 seconds. The saved table also refutes
candidate 6 in the original search numbering; it refutes none of the other
59 candidates that had survived the earlier matrix tests. They remain research
candidates. Further order-six searches for candidates 12, 14, and 15 each
timed out after 240 seconds; no conclusion follows from those timeouts.
The existing data file and independent replayer now include this counterexample
and remove candidate 6 from the surviving list. Catalogue counts are unchanged.

## E714 right division: recover the square, but not yet multiplication

[`Equation714RightImage.lean`](../equational_theories/Parastrophes/Equation714RightImage.lean)
proves two necessary constraints on arbitrary carriers. If R is the right
division of an E714 magma M, then

```
R(R(R(x,x),x),x) = M(x,x)
R(R(x,R(x,y)), R(y,R(x,y))) = R(x,y).
```

The first uses the known formula `R(x,y)=M(y,M(y,M(y,x)))`: four applications
of the x-row to x return x, so nine applications give M(x,x). The second
comes from flexibility of M, also proved in that module, followed by
eliminating multiplication with the inverse identities. These are necessary
conditions only, with no claim of an exact basis or a closed catalogue row.

A binary multiplication-recovery search on six repository models and 65
homogeneous prime-field affine models reached two million value signatures,
completing every subterm layer through nine operations and part of layer ten.
It found no recovery term. This bounded search does not exclude longer terms.


## E1085: an exact conditional criterion and two recovery obstructions (4 November 2026)

**No additional single-equation row is closed in this pass.** Among operations
with bijective rows, E1085's left-division image is characterized exactly by

```
y * (x * z) = y  →  z * (y * x) = x.
```

This is a quasiidentity, not an ordinary equation or an equational basis.
Both directions hold on arbitrary carriers and are formalized in
[`Equation1085ImageCriterion.lean`](../equational_theories/Parastrophes/Equation1085ImageCriterion.lean).
The antecedent says that z is the source product x*(y*y); the consequent is
E1085 written using division. This permits finite searches over just one table,
without guessing a term for the source square or introducing a second table.
The same file proves that the source square map is injective whenever left
division exists, and therefore bijective on finite carriers.

Two eight-operation square-recovery guesses are now refuted in Lean by models
of orders seven and nine. The latter guess passed exhaustive research searches
through order eight before the direct division-table search found its
nine-element counterexample. Only the positive counterexamples, not those
UNSAT searches, are used in Lean. The source laws, inverse tables and failures
are small kernel checks in
[`Equation1085SquareCounterexample.lean`](../equational_theories/Parastrophes/Equation1085SquareCounterexample.lean).
The symbolic criterion and both examples take approximately 2.5 and 4 seconds,
respectively, to build locally.

The square-term search now includes the earlier nonlinear search witnesses as
well as the repository-table inventory. Previously it could miss models saved
in `finite_images_20261027.json`. After adding the new witnesses, the bounded
search excludes square-recovery terms through nine operations on this sample
pool. Its next eighteen-operation candidate was subsequently refuted by another
nine-element model, now also checked in Lean. This does not
exclude a different recovery term or a single-equation characterization.
The tables, exact rejected terms, candidate and search scopes are saved in
[`e1085_image_research_20261104.json`](../data/parastrophes/e1085_image_research_20261104.json).


## E714 and E1085: fixed points and further recovery obstructions (4 November)

No single-equation catalogue row closes in this pass. For E714, the formalized
flexibility argument gives a useful restriction on every left translation L:
`L³(y)=y` if and only if `L(y)=y`. Indeed the known right-division formula
turns `L_x³(y)=y` into `y*x=y`; flexibility and left cancellation then give
`x*y=y`. This excludes three-cycles, but does not exclude six-cycles or every
cycle with length divisible by three. The proof works on arbitrary carriers
and is in `Eq714RightImage.row_cube_fixed_iff`.

Squaring need not preserve multiplication in an E714 source: a six-element
counterexample is checked in the same module. For E1085, a third proposed
square-recovery term, this time with eighteen operations, fails in a
nine-element model. In that example division's own square map is not
injective, although source squaring is bijective by the general theorem.
Both counterexamples use small kernel checks; no external search result is
assumed. Their tables have been added to the research sample pool.


## Two remaining converses reduced more precisely (4 November)

For the E917 fifty-operation proposal, `TwoShifts.basis_of_fixed_point` now
proves that a **single** fixed point of its common F-map implies the whole
image basis. No existence of such a point is asserted. Consequently a bad
candidate model has no fixed points anywhere. The normalized middle term
has also been proved explicitly as
`(f⁻¹(a(x))*(U(x)*f(a(x))))*g(a(x))`; replacing that inverse by f would change
the proposed equation. These reductions register no characterization.

For E1516, the proposal is `y*(y*(x*y))=c(x)` together with
`c(x)*(x*c(x))=x`, where `c(x)=x*(x*(x*x))`. The new
`characterizes_turn_injective_fin` theorem proves that adding injectivity of
c makes this an exact finite characterization. Every actual image has
bijective c. A search for `c(0)=c(1)` therefore covers all countermodels to
this pair at a given order, up to relabeling. CaDiCaL found no order-eight
countermodel in about 193 seconds; order nine timed out after ten minutes.
These searches are research evidence only, with no Lean UNSAT certificates.
The unrestricted converse was subsequently refuted by the 38-element
construction below, under "E1516: a small formula refutes Common + Short".
The single-equation question remains open.


The larger E714 right-division recovery search reached fifteen million distinct
value signatures on seven saved source tables and 65 homogeneous affine
models. It found no multiplication-recovery term. Subterm layers through nine
operations were completed and layer ten was partial; the root lookup excludes
all recovery terms through ten operations on these samples and checks some
larger ones. This is not a nonexistence proof for arbitrary terms. The exact
bounds and sample inputs are saved in
[`e714_square_research_20261104.json`](../data/parastrophes/e714_square_research_20261104.json).

## E917: a new composition candidate and its exact affine case (4 November)

**The unrestricted image question remains open.** Write

```
q(x)=(x*(x*x))*x       U(x)=x*q(x)
F(x,y)=y*(q(x)*(x*y))  G(y,x)=q(y*x)*((y*x)*y).
```

The new candidate is `F(F(G(r,G(s,G(t,G(v,U(x))))),z),y)=x`, with all
seven variables independent. Its expanded size is **101536 operations**;
named subterms keep the Lean proof small. No minimality or unrestricted
characterization is claimed.

[`Equation917CompositionCandidate.lean`](../equational_theories/Parastrophes/Equation917CompositionCandidate.lean)
proves that every actual image satisfies it. Conversely, finiteness turns
each factor of the composition into a permutation. Varying the independent
parameters gives common permutations `F(x,y)=a(x)` and `G(y,x)=b(x)`, and
the operation is a quasigroup. The remaining conditions include
`x*b(y)=a(x*y)` and `a² b⁴ U=id`, with that precise composition order.
A fixed point of a would force a and b to be the identity, hence U as well,
and recover the exact image basis. A power of a fixing one point also fixes
every point, so all of its cycles have the same length. Existence of a fixed
point, and even commutation of a with b in this candidate, remain unproved.

There is a complete restricted converse in
[`Equation917CompositionAffine.lean`](../equational_theories/Parastrophes/Equation917CompositionAffine.lean):
the candidate characterizes the image among all operations `x*y=A*x+B*y+d`
on **finite commutative rings**. Independence forces `A=-B³`; the common maps
then act by translations. The composition forces U's linear part to be one,
and an integral Bezout identity eliminates the remaining translations.
Its constant is one, so the proof covers every characteristic and rings with
nilpotents, not just the sampled prime fields.

External Mace4 searches exhaust counterexamples at orders 2–9. For order 9,
the uniform-cycle lemma reduces the possibilities to one 9-cycle or three
3-cycles; both searches finish in about 110 CPU seconds. At orders 10 and 11
the searches time out after 240 CPU seconds. These are research computations,
not Lean nonexistence certificates. Inputs, scope, and results are recorded in
[`e917_composition_candidate_20261104.json`](../data/parastrophes/e917_composition_candidate_20261104.json).
The two new modules and the full parastrophe target build successfully. Their
axiom audits contain only Lean's standard axioms. Catalogue counts remain
unchanged: **39 finite image gaps per side, 4628 fully settled finite rows**.

A further proved reduction handles involutions more efficiently. Two instances
of the common identities give `q(q(x))=x*x` exactly when `a(x)=b(x)`.
If U is the identity, agreement at a single point forces both maps to be the
identity. If a is an involution, conjugacy makes b an involution too, and the
composition forces U to be the identity. A bad model in this case therefore
has two perfect matchings with no common edge. At order 10 their alternating
cycles have only two possible patterns: one 10-cycle, or a 4-cycle and a
6-cycle. Fixing these patterns makes both Mace4 searches finish in under a
second. Thus the **involution case at order 10** is excluded by research
computation; the cases with common-map cycles of lengths 5 and 10 remain open.

### Further reductions and a Mal'cev obstruction

**No additional single-equation row closes here.** The composition candidate
now has a proved converse under the extra hypothesis **a=b**:
`CompositionCandidate.basis_of_equal_maps`. The algebraic part does not need
finiteness or the composition identity. Equality of the maps gives
`x*a(y)=a(x*y)`, `q(a(x))=a²(q(x))`, and `a⁴=id`. The composition then gives
`U=a²`, while `q(q(x))=x*x` makes the diagonal F identity force `a=id`.
Establishing a=b from the candidate alone remains open.

[`Equation917CyclicCoordinates.lean`](../equational_theories/Parastrophes/Equation917CyclicCoordinates.lean)
formalizes another search reduction. If a is one cycle, conjugacy along a row
makes b one cycle too. Labeling a by addition of one modulo n expresses the
entire multiplication as `u(x)+v(y)`, with two permutations u and v and
`v(0)=0`. These permutations need not be additive. Mace4 searches in these
coordinates at orders 10 and 11 each time out after 180 CPU seconds; neither
order is excluded. Twenty further spaces of central offsets over the ten
saved image quotients, with fibre F73 and coefficients B=27 or 46, contain no
counterexample. That is a restricted research computation, not a theorem
about all extensions.

A tempting Mal'cev compression is definitively refuted in
[`Equation917MalcevCounterexample.lean`](../equational_theories/Parastrophes/Equation917MalcevCounterexample.lean).
Put `H(x,y)=q(x)*(x*y)`, `R(x,w)=H(H(w,q(x)),x)`, and
`p(x,y,z,w)=R(x,w)*H(U(z),R(y,w))`. Every actual image satisfies the two
Mal'cev identities for p, as the module proves on arbitrary carriers.
Conversely, the quasigroup `x*y=b³*x+b*y+1` over
`F8=F2[b]/(b³+b+1)` satisfies both identities but has `U(0)=2` in binary
coefficient encoding. Lean checks the eight-element table, bijectivity, both
identities, and failure of image membership. This rules out that proposed
compression, not every single-equation characterization. It also explains
why testing only prime fields missed the obstruction.

The E1516 two-equation proposal remains open too: a normalized Mace4 search
for an order-nine collision of its turn map times out after 300 CPU seconds.
Catalogue counts are unchanged: **39 finite image gaps per side, 4628 fully
settled finite rows**.

### E917 sandwich candidate: the converse proved at every prime order

[`Equation917SandwichCyclic.lean`](../equational_theories/Parastrophes/Equation917SandwichCyclic.lean)
proves `SandwichCandidate.characterizes_prime_card`: the **782-operation
sandwich identity** exactly characterizes the E917 left-division image at
every prime order. This is different from the 101536-operation composition
candidate discussed above. The composite-order converse, and hence the
unrestricted catalogue row, remain open.

The key step excludes a single common-permutation cycle of **any** length.
In cyclic coordinates write a(x)=x+1. The already proved commutation of a
with b and c makes b(x)=x+beta and c(x)=x+gamma. Row conjugacy gives
`x*y = x*0 + gamma*y` and `beta*gamma=1`. The simultaneous-shift identity
then gives `x*0=d-gamma³*x`. Thus the entire magma is affine over Z/n,
where the existing integral Bezout proof forces the image basis and a=id.
The new module constructs the cyclic labeling, so the result also applies
to arbitrary finite carrier types, not merely tables already in that form.

Finally, a power of a fixing one point fixes every point. All nontrivial
cycles therefore have the same length, which divides the carrier size.
At prime order, a is either the identity or one full cycle. The full-cycle
case has just been excluded; a=id forces b=c=U=id and the exact image basis.
Lean proves the cycle argument and the converse uniformly over all primes.
There are no finite tables, external UNSAT certificates, or new axioms in
this proof. No `SingleEquation .fin` attribute is added, since that would
incorrectly include the still-unresolved composite orders.

### E917: a twenty-operation candidate and the characteristic-eleven trap

**No further catalogue row closes in this pass.** There is now a substantially
shorter candidate for the finite left-division image. With the same q, U and H
as above, it is

```
x = ((U(w)*(U(z)*y))*v) * H(x,(w*(z*y))*v).
```

The five variables are independent, and expansion uses **20 operations**.
[`Equation917DoubleUnitCandidate.lean`](../equational_theories/Parastrophes/Equation917DoubleUnitCandidate.lean)
proves the forward implication, surjective rows on arbitrary carriers, and
the quasigroup consequence on finite carriers. Its exact finite reduction
gives permutations a,b,c satisfying `U(x)*y=a(x*y)`, `x*a(y)=b(x*y)`,
`a(b(x))*y=c(x*y)`, and `c(y)*H(x,y)=x`. The pairs a,b and b,c commute.
A power of U fixing one point fixes every point; one fixed point of U would
give the entire image basis. Establishing that fixed point remains open.

[`Equation917DoubleUnitAffine.lean`](../equational_theories/Parastrophes/Equation917DoubleUnitAffine.lean)
proves the **complete affine converse over every commutative ring**. A
surjective row makes B a unit. Comparing the coefficients of v, x and w
gives `A=-B³` and the same `P(B)=Q(B)=0` as in the sandwich proof. Put
`C=(B+1)(B²+1)` and `K=B³-B+1`. The constant coefficient gives `C*W*d=0`,
where `W=B¹²+B¹¹−B¹⁰−B⁹+B⁵−B³+1`. An integral Bezout identity for K and W
has constant one, so `C*d=0` and both unwanted translations vanish. Lean
checks this uniformly, including infinite rings and nilpotents.

The second U insertion matters. Replacing U(w) by w gives a **16-operation
false candidate**, despite its successful characteristic-zero calculation.
The quasigroup `x*y=7x+5y+1` over Z/11 satisfies it but violates U=id. Its
relevant integral resultant is eleven. Both the counterexample and its
exclusion by the twenty-operation candidate are checked in
[`Equation917SingleUnitCounterexample.lean`](../equational_theories/Parastrophes/Equation917SingleUnitCounterexample.lean).
Research checks also find no counterexample in 390 spaces of central offsets
over the ten saved image quotients, with scalar fibres at primes through 53.
Those computations are not a general converse. Exact inputs and scope are in
[`e917_double_unit_20261104.json`](../data/parastrophes/e917_double_unit_20261104.json).

### E917: asymmetric powers and a stronger supply of test models

**The single-equation row remains open.** A new candidate is

```
x = ((U(U(w))*(U(z)*y))*v) * H(x,(w*(z*y))*v).
```

This has **40 operations** after expansion: U repeats its argument five times,
so U(U(w)) alone has 24 operations. All image models satisfy it.
[`Equation917PowerComparison.lean`](../equational_theories/Parastrophes/Equation917PowerComparison.lean)
proves that all its rows are surjective even on arbitrary carriers, and that
finite models are quasigroups. The precise finite reduction is to bijections
satisfying `U(x)*y=a(x*y)`, `x*a(y)=b(x*y)`,
`a(a(b(x)))*y=c(x*y)` and `c(y)*H(x,y)=x`. The pairs a,b and b,c commute;
commutation of a,c is not assumed. U has uniform cycle lengths, and one fixed
point of U would give the full image basis. That fixed-point step is open.

The asymmetric powers remove an obstruction left by the twenty-operation
candidate. In a crossed magma where `x*U(y)=w(x*y)`, the previously proved
regularity identities give `U(x)*y=U(x*y)` and `w=U⁻¹`. The old comparison
then holds automatically, whereas the new comparison simplifies to `x=U(x)`.
Both statements are now proved in
[`Equation917RegularUnit.lean`](../equational_theories/Parastrophes/Equation917RegularUnit.lean).
This conditional converse does not assume that every candidate is regular.

[`Equation917PowerAffine.lean`](../equational_theories/Parastrophes/Equation917PowerAffine.lean)
proves the full converse for affine operations over **every commutative ring**.
The variable coefficients again give A=−B³ and P=Q=0. With
`C=(B+1)(B²+1)` and `K=B³−B+1`, the constant coefficient gives `C*W*d=0`,
where `W=B¹²+2B¹¹−B¹⁰−2B⁹+B⁵−B³+1`. An integral Bezout identity for K,W
has constant one, forcing `C*d=0` and the image basis. Thus this result also
covers rings with nilpotents. By contrast, inserting U in all three inner
slots gives a false 24-operation candidate: `23x+3y+1` on Z/25 satisfies it
but has U(0)=5. That counterexample is checked in
[`Equation917SingleUnitCounterexample.lean`](../equational_theories/Parastrophes/Equation917SingleUnitCounterexample.lean).

The model pool also needed strengthening. An eight-element actual image has
`q(f(0))≠q(0)` and `f²(0)≠0`, where `f(x)=q(x)*x`. Two binary central
extensions of it, each of order sixteen, refute `f⁴=id` and `q∘f²=q`
respectively. These auxiliary identities must not be used in a converse.
All three image-membership proofs and all four failures are kernel-checked in
[`Equation917UnaryCounterexamples.lean`](../equational_theories/Parastrophes/Equation917UnaryCounterexamples.lean).
The supplemental data preserves the historical ten-model pool unchanged.

Research checks find no counterexample to the new candidate in **507 spaces
of central offsets**, using thirteen image quotients and scalar fibres at
primes through 53. Each check solves the entire linear system for that space;
it is not a general converse. Mace4 exhausts the reduced system at orders 2–5
and times out separately at orders 6–9. Three 600-second equational-prover
attempts, and a 240-second involution-specialized attempt, find no proof. A separate
600-second Vampire portfolio also times out.
Inputs and scope are saved in
[`e917_power_comparison_20261104.json`](../data/parastrophes/e917_power_comparison_20261104.json);
[`check_parastrophe_e917_power.py`](../scripts/check_parastrophe_e917_power.py)
replays the model data and offset spaces. The full parastrophe target builds,
and the new proofs use only standard Lean axioms. Inventory remains
**39 finite image gaps per side, 4628 fully settled finite rows**.

### E477: an arbitrary-carrier cancellation and surjectivity argument

**No single-equation row closes here.** The existing criterion is the pair
E411 + E4332 together with bijective rows. Write `c(x)=x*(x*x)` and
`v(x)=x*c(x)`. The basis gives `x*(y*x)=c(y)`, `x*v(x)=x`, and
`c(v(x))=v(x)`. Row cancellation makes c injective: if c(a)=c(b),
crossing identifies the rows indexed by a and b, and cancelling twice in
their diagonal values gives a=b. Consequently columns are injective too.

Surjectivity has a separate short proof that needs no finiteness. Given x,
solve `v(x)*y=x` using a surjective row. Crossing gives `y*x=v(x)` and
then `c(y)=x*v(x)=x`. Thus c is onto. The rotated crossed law
`(a*b)*c(a)=c(b)` now makes every column onto. **Every actual left-division
image of E477 is a full quasigroup, including on infinite carriers.** This
assumes that the source admits left division; it does not settle division
existence for arbitrary E477 sources.

These results are proved in
[`Equation477Image.lean`](../equational_theories/Parastrophes/Equation477Image.lean),
particularly `core_injective_of_rows`, `core_surjective_of_rows`, and
`image_quasigroup`. The finite image criterion can equivalently be written
as the two existing identities plus injectivity of c
(`inImage_iff_core_injective`). The six-element counterexample to dropping
the extra condition remains valid.

### E481: a seven-element loop catches a failure missed by large towers

**The finite single-equation question remains open.** A new candidate was
`x=f³(f(x)*(x*f⁵(x)))`, with `f(x)=e*x`. Counting e as a constant, this has
eleven operations. It survived the tested central towers, including
division structures of order 1,771,561 and random choices of the free
central offsets. Mace4 nevertheless found a seven-element cross-inverse
loop refuting it in about 0.01 CPU seconds. Its inverse has the five-cycle
`1→2→3→4→6→1`, fixes 0, and also fixes the nonunit element 5. These features
are absent from the earlier tower family, whose nontrivial inverse cycles
are even and whose only fixed point is the unit.

The Cartesian-square division has order 49 and sends the candidate at
(0,1) to (0,0).
[`Equation481SmallLoop.lean`](../equational_theories/Parastrophes/Equation481SmallLoop.lean)
checks the small loop, applies the general image construction, and proves
this failure in Lean. Only the seven-by-seven loop table is stored, with
no large division table or solver certificate. The module builds in about
four seconds. Data is in
[`e481_small_loop_20261104.json`](../data/parastrophes/e481_small_loop_20261104.json).

The term search now accepts `--small-loop`. With that sample it exhausts
all defining identities through **eleven operations**, using 1,457,357
tagged evaluation signatures. The reduction covers identities with any
number of variables: assign every variable other than the isolated side x
to e, and retain the leftmost-variable tag when merging signatures.
This bound is **a Python research computation, not a Lean theorem** and
not an exclusion of longer identities. Exact scope and the replay command
are saved in
[`e481_small_loop_search_20261104.json`](../data/parastrophes/e481_small_loop_search_20261104.json).
The catalogue counts remain unchanged.

### Composing images identifies a duplicated finite question

[`ImageComposition.lean`](../equational_theories/Parastrophes/ImageComposition.lean)
now proves a general dependency between the two image questions. If the left
divisions of L are exactly K, and every L model admits left division, then
the right-division images of L and K differ only by taking the opposite
operation. A single defining equation for either right image therefore gives
one for the other, by dualizing that equation. Negative answers transfer too.
The same statement holds with left and right exchanged. The proof requires
only the known side of division, not an assumed full quasigroup structure.

In particular, **E464 right and E511 right are one independent finite
single-equation problem**, as proved by `right464_iff_right511_fin`.
E714 belongs to E511's finite implication class, so its right-image question
is already included. This reduces duplicated research; it is not a positive
or negative answer to any of these cells. An audit of the current catalogue
found no open cell whose answer follows immediately by this new transfer
from an already answered cell. Consequently no characterization attribute
or changed proof status is attached.

The E1516 converse remains unresolved after a further 180-second Vampire
portfolio for injectivity of its common map, a 90-second Prover9 attempt
under the extra hypothesis that the map is idempotent, and Mace4 searches
for a collision at orders nine (60 CPU seconds) and ten (90 CPU seconds).
All four attempts timed out; none proves an exclusion or a characterization.


### E917: the full additive converse and exhaustive nonabelian isotope checks

**No catalogue row closes here.** The forty-operation candidate is now proved
sufficient for every operation `x*y=a(x)+b(y)+k` on **any abelian group**, with
arbitrary additive endomorphisms a,b. Neither commutation nor bijectivity nor
finiteness is assumed. Comparing the free outer parameter with zero forces
`a=-b³`; surjective rows make b onto, and a collision of b would give equal
right sides of the candidate for distinct x. Thus both coefficients are
bijective and commute. These steps are checked in
[`Equation917AdditiveCoefficients.lean`](../equational_theories/Parastrophes/Equation917AdditiveCoefficients.lean).

[`Equation917ModuleConverse.lean`](../equational_theories/Parastrophes/Equation917ModuleConverse.lean)
finishes the converse, including mixed torsion and infinite groups. Regard the
group as a module over Z[X], with X acting as b. The earlier polynomial
calculation now gives annihilators of vectors, without assuming the module is
faithful. The same integral Bezout identity, whose constant is one, kills the
remaining offset and gives both image identities. `Additive.characterizes`
proves the exact image equivalence for this construction family. This does
not assert that every candidate magma has an additive representation.

The research search also exhausts group isotopes of **every group through
order seven**, and of both nonabelian groups of order eight. For the latter,
normalizing the first input permutation at the group identity and then using
group automorphisms leaves **101,606,400** pairs for D8 and **76,204,800** for
Q8. None refutes the candidate. These are bounded Python checks, not Lean
exclusions and not searches over all quasigroups. The separate searches for
arbitrary order-eight quasigroups, with the comparison permutation normalized
to cycles of length 2, 4 or 8, each timed out after 120 CPU seconds.

The saved data and replayers are
[`e917_group_isotopes_20261104.json`](../data/parastrophes/e917_group_isotopes_20261104.json),
[`check_parastrophe_e917_group_isotopes.py`](../scripts/check_parastrophe_e917_group_isotopes.py),
[`e917_nonabelian_isotopes_20261104.json`](../data/parastrophes/e917_nonabelian_isotopes_20261104.json)
and
[`check_parastrophe_e917_nonabelian_isotopes.py`](../scripts/check_parastrophe_e917_nonabelian_isotopes.py).

### E477: an arbitrary translation in the cubic map

**The finite single-equation question remains open.** There is now a simple
family showing why a bounded cubic-map period cannot supply its inverse.
For an abelian group G and k in G, take two copies A and B and define

```
A(x)*A(y) = B(y-x)       A(x)*B(y) = A(x+k-y)
B(x)*A(y) = A(x+y)       B(x)*B(y) = B(-x-y).
```

This is an actual left-division image of E477. The original multiplication
is given explicitly by reversing each row; checking the four choices of
layers proves both image identities. Its cubic map `c(x)=x*(x*x)` translates
A by k and fixes B. Hence `c^n(A(x))=A(x+n*k)`. Taking G=Z/(n+1) and k=1
refutes every proposed positive uniform period n, already in a finite image
of order 2(n+1); taking G=Z gives an infinite orbit. All of this, including
`no_uniform_finite_period`, is proved in
[`Equation477TranslationFamily.lean`](../equational_theories/Parastrophes/Equation477TranslationFamily.lean).
It rules out recovering the inverse by a fixed power of c, **not** recovering
it by an arbitrary magma term.

A bounded unary-term search found a fourteen-operation inverse proposal that
passed 58 samples, but Mace4 immediately refuted it with a seven-element
image. Its table and the exact failed term are retained in
[`e477_core_research_20261104.json`](../data/parastrophes/e477_core_research_20261104.json)
as Python-checked research data. The earlier nine- and ten-element period
counterexamples are also retained there; the new formula makes their role as
period obstructions redundant. No failed proposal is registered as a theorem.

### E1518: uniform recovery, finite products, and deeper term obstructions

**The finite uniform-term row remains open.** There is now an exact Lean
reduction of that question, and finite obstructions covering all shallow
terms rather than a sample of proposed formulas.

Write `S(x)=x*x`. In a finite E1518 model, S and every left translation are
bijective. If `r(x)*r(x)=x`, left division is `y*(r(x)*y)`; conversely, left
division at `(x,x)` is r(x). Thus a uniform division term exists exactly when
a uniform unary inverse-square term exists. This equivalence is proved in
[`Equation1518Uniform.lean`](../equational_theories/Parastrophes/Equation1518Uniform.lean),
without restricting the shape or length of the term.

[`Equation1518FinitePool.lean`](../equational_theories/Parastrophes/Equation1518FinitePool.lean)
then removes a subtler dependence on the model and the point. If a fixed finite
pool of terms supplies a square root at every point of every finite model,
one term in the pool must work everywhere: otherwise take a pointed finite
countermodel for each term and form their direct product. Whichever term
works at the product point fails in its own coordinate. Consequently
`recovery_iff_bounded_pointwise` proves that uniform finite division is
equivalent to a **uniform bound on pointwise root-term depth**. This argument
uses finite products, not an assumption that finite-only recovery follows
from arbitrary-carrier compactness.

Two new finite models give rigorous lower bounds. A central extension of the
old fifteen-element seed gives a 45-element model requiring depth five at its
distinguished point. Extending that model by F3² gives a **405-element model
requiring depth six**. Its successive sets of generated values have sizes
`1, 2, 4, 12, 93, 390, 405`: even the 390 values available through depth five
omit the required square root. The Lean proofs check layer closure and then
induct over arbitrary terms; an explicit term attains the stated depth in
each model. Depth counts nested products, not the total number of products.

The construction remains small. For a base B, use
`(i,u)*(j,v)=(B(i,j),v+c(i,j))`. E1518 reduces to
`c(y,x)+c(x,B(y,x))+c(S(y),B(x,B(y,x)))=0`.
The 45-element base has an 85-dimensional space of solutions over F3. The
research calculation first uses all these coordinates, then projects to two
coordinates while preserving the failure of every depth-five term. Lean
checks the retained offsets independently of that calculation; it needs only
2025 pairs of ternary offsets, stored as packed integers, and small layer
certificates. No external SAT certificate, `native_decide`, or `sorry` is used.
The proofs are in
[`Equation1518TermDepth.lean`](../equational_theories/Parastrophes/Equation1518TermDepth.lean)
and
[`Equation1518TermDepthSix.lean`](../equational_theories/Parastrophes/Equation1518TermDepthSix.lean).
The independent
[`replayer`](../scripts/check_parastrophe_e1518_term_depth.py)
also checks the complete finite multiplication tables and the attaining terms.

This does **not** yet construct models requiring arbitrarily large depth.
Nor does it rule out a longer uniform term. Two 300-second Prover9 searches
for a general inverse-square term timed out without a proof. No positive or
negative uniform-recovery attribute is attached to these partial results.

There is also a useful explanation of the old fifteen-element seed. It is a
three-block affine operation on `Fin 3 × F5`, using a square root i of −1.
More generally, the coefficient tables in
[`e1518_three_block_affine_20261104.json`](../data/parastrophes/e1518_three_block_affine_20261104.json)
work over a commutative ring with `i²=-1` and `2h=1`. Squaring sends
`(0,u) → (1,u) → (2,u) → (0,i*u)`, explaining its twelve-cycle.
The
[`symbolic replayer`](../scripts/check_parastrophe_e1518_affine.py)
checks all eighteen law coefficients in Z[1/2,i]/(i²+1) and identifies every
entry of the old seed. This general affine family is **research proved by
exact symbolic calculation, not yet formalized in Lean**; its period bound
does not apply to the larger central extensions.

### E1516: complete characterization of the commutative division images

**The unrestricted single-equation row remains open.** There is now an exact
description of its commutative subfamily, on finite **and infinite** carriers.
A commutative operation D is a left-division image of E1516 precisely when

```
D(x,x) = x
D(y,D(y,D(y,x))) = x.    (E75)
```

The original multiplication is `M(x,y)=D(x,D(x,y))`. These two operations
are inverse row by row. This does not require the original M to be commutative.
The characterization is proved in
[`Equation1516Commutative.lean`](../equational_theories/Parastrophes/Equation1516Commutative.lean),
as `commutative_image_iff_idempotent75`. The same module proves that the
previous proposal `Common + Short` is sufficient throughout the commutative
class, without finiteness (`characterizes_commutative`).

Here is the cancellation argument behind the result. Common makes every row
cube equal to the same map c, so c commutes with every row. With
`u(x)=D(x,D(x,x))`, Short gives `c²(u(x))=x`. Moving c through the products
also gives `u(c(x))=c³(u(x))=c(x)`. Thus c is onto, u is the identity, and
c² is the identity. Applying the same rules to the diagonal forces c=id
and D(x,x)=x. For the forward direction on infinite carriers, the source
square is an inverse to the cube of any division row; cancellation supplies
the inverse identity that the earlier proof obtained from finiteness.

An attractive shortcut for the noncommutative case is **false**: the common
map need not be an endomorphism, even in an actual image. The existing
133-element extension already fails preservation of the square at (0,0).
`Equation1516Extensions.turn133_not_endomorphism` verifies this using the
previously proved model, without another table. Both modules build and their
new theorems use only standard Lean axioms. No unconditional characterization
attribute is attached, and the catalogue counts are unchanged.

### E1516: a small formula refutes Common + Short

**The proposed two-identity characterization is false, even on finite
carriers. The single-equation catalogue row remains open.** The earlier
missing injectivity of the common map cannot be proved from these identities.
There is now a 38-element counterexample, proved in
[`Equation1516CommonCounterexample.lean`](../equational_theories/Parastrophes/Equation1516CommonCounterexample.lean).
It replaces the stalled search for a converse with a definite obstruction.

The construction has a short formula. Take `(i,u)` in `Z/19Z × Z/2Z`.
For inputs `(i,u)` and `(j,v)`, put `d=j-i`. The first output coordinate is
`-2i+3j+1`; the second is `u+v` when d=13, v when d is 4, 8 or 11,
and zero otherwise. In the three products
`y*(y*(x*y))`, the successive differences are d, 2d+1 and 6d+4.
All second coordinates vanish: only d=0,7,11,17 need attention, and d=11
reduces to `v+v=0`. Consequently `c(i,u)=(i+13,0)`. The two products
`c(x)*(x*c(x))` have differences 13 and 8, so they recover x exactly.
Nevertheless the row at `(0,0)` identifies `(0,0)` and `(0,1)`, ruling out
membership in the actual division image. This argument works with any
nontrivial abelian group of exponent two in the second coordinate, including
infinite ones. The Lean proof uses the formula and nineteen residue checks;
there is no multiplication-table certificate, external proof certificate,
`native_decide`, or `sorry`.

The useful change in the search was an **idempotent-free quotient**. The
19-element operation `D(i,j)=-2i+3j+1` is an actual image, with original
multiplication `M(i,j)=7i+13j+6`; its diagonal is `i+1`. Both facts are
formalized in the same module. Earlier extension searches over idempotent
quotients could get stuck on a small closed fibre before exploring the desired
failure of cancellation. A Boolean search over arbitrary two-element fibres
of this new quotient found the first counterexample. Restricting the fibre
rule to depend on j-i, and simplifying it, produced the formula above.
The genuine 19-element **source** model has been added to the shared sample
pool; the 38-element counterexample is kept separate from genuine models.
The data and independent finite replayer are
[`e1516_common_counterexample_20261104.json`](../data/parastrophes/e1516_common_counterexample_20261104.json)
and [`check_parastrophe_e1516_common.py`](../scripts/check_parastrophe_e1516_common.py).

There are two accompanying Lean results in
[`Equation1516ColumnCriterion.lean`](../equational_theories/Parastrophes/Equation1516ColumnCriterion.lean).
First, `Short` is exact among finite **right** quasigroups too. Column
injectivity extracts Common; surjective columns identify the range of c with
the range of each squared row. That range is stable under all rows, and Short
then makes it the whole carrier. Finiteness supplies row injectivity.
Second, the old four-element counterexample refutes every proposed identity
obtained from Short by replacing its two common-map occurrences with
`R_x^k(cross(x,y))` and `R_x^l(cross(x,z))`, for arbitrary natural k,l.
Its relevant right-translation orbits have period two, so four small checks
cover the entire infinite family. Neither result is registered as an
unconditional single-equation characterization, and catalogue counts do not
change.

### E917: all outer unit powers are ruled out (4 November 2026)

**This closes an infinite family of candidate identities, not the unrestricted
single-equation catalogue field.** Put `q(x)=(x*(x*x))*x`, `U(x)=x*q(x)`, and
`H(x,y)=q(x)*(x*y)`. Every finite left-division image of E917 satisfies

```
U^[k](y) * H(x,y) = x.
```

However, **for every natural k, including zero**, a finite quasigroup satisfies
this proposed identity while failing the image's necessary identity `U(x)=x`.
Thus no choice of iteration count repairs this particular crossed identity,
even if quasigroup status is assumed separately.

Six operations `D(x,y)=a*x+b*y` on Z/p suffice for all k:

| k modulo 12 | p | a | b | U(x) |
| --- | ---: | ---: | ---: | --- |
| 0, 4, 8 | 29 | 18 | 15 | 17x |
| 1, 5, 9 | 197 | 25 | 166 | 183x |
| 3, 7, 11 | 37 | 14 | 33 | 6x |
| 2 | 157 | 154 | 89 | 135x |
| 6 | 13 | 12 | 10 | 2x |
| 10 | 13 | 4 | 4 | 11x |

Writing `Q=a²+a²b+ab²+b` and `u=a+bQ`, symbolic evaluation gives
`q(x)=Qx`, `U(x)=ux`, and coefficients `ab(Q+b)` and `au^k+b³` for x and y
in the candidate. The saved coefficients make these 1 and 0 respectively.
In every seed, `u^12=1` but `u≠1`; reduction modulo twelve therefore proves
the result for arbitrarily large exponents. Explicit inverses of a and b
establish both sides of quasigroup cancellation and division.

[`Equation917OuterPowers.lean`](../equational_theories/Parastrophes/Equation917OuterPowers.lean)
proves `counterexample` and `no_characterization` uniformly in k. The kernel
checks twelve selections from six five-number seeds, with no multiplication
table, external certificate, native decision, or enumeration of element pairs.
The compact [data](../data/parastrophes/e917_outer_powers_20261104.json) is
independently replayed by
[`check_parastrophe_e917_outer_powers.py`](../scripts/check_parastrophe_e917_outer_powers.py).
No characterization attribute is attached, so catalogue counts are unchanged.

The same pass strengthened the E1315 square-recovery samples. Nine proposed
unary terms (13–19 operations) that successively passed the saved examples
were each refuted by an eight-element source model found by Mace4. The source
laws, bijective rows, division tables, and failed evaluations are independently
replayed by
[`check_parastrophe_e1315_square.py`](../scripts/check_parastrophe_e1315_square.py).
These are **Python-checked research examples, not Lean results**. Their
[data file](../data/parastrophes/e1315_square_counterexample_20261104.json)
feeds the existing sample loader, preventing those same guesses from being
rediscovered. They do not exclude all recovery terms or resolve an image field.

## E917: a shorter comparison fails at order 25 (4 November 2026)

**No additional single-equation catalogue row closes in this pass.** With
`q(x)=(x*(x*x))*x`, `U(x)=x*q(x)` and `H(x,y)=q(x)*(x*y)`, consider

```
x = (U(z)*y) * H(x,z*y).
```

This twelve-operation identity holds in every E917 left-division image. It
forces surjective rows on arbitrary carriers and a quasigroup on finite
carriers. In the finite, nonempty case it is equivalent to having a permutation
`a` with `U(x)*y=a(x*y)` and `a(y)*H(x,y)=x`. A fixed point of U would force
U to be the identity and finish the converse. These reductions are proved in
[`Equation917LeftComparison.lean`](../equational_theories/Parastrophes/Equation917LeftComparison.lean).

**That missing fixed point need not exist.** A central extension of a genuine
five-element image gives a counterexample on 25 elements:
`(i,u)*(j,v)=(B(i,j),3u+3v+φ(i,j))`, with fibre arithmetic modulo five.
Here `U(i,u)=(i,u+1)` and `a(i,u)=(i,u+3)`. The image basis requires `U=id`,
so this is not an image even though it is a quasigroup satisfying the proposed
identity. Lean proves the formulas for q and U by five cases on i and the
crossed identity by 25 cases on `(i,j)`, with symbolic arithmetic in the
fibres. It does not enumerate all triples of the 25-element carrier. The
module built in about 15 seconds locally; the axiom audit uses only the usual
`propext`, `Classical.choice`, and `Quot.sound`.

The [compact data](../data/parastrophes/e917_left_comparison_20261104.json)
stores the five-element base and 25 offsets. The independent
[`replayer`](../scripts/check_parastrophe_e917_left_comparison.py) also checks
the whole candidate directly. Discovery used linear equations for the offsets,
not a search over all 25-element multiplication tables.

Two further research candidates survived the same 390 scalar central-extension
spaces: `x=(w*(U(z)*y))*H(x,w*(z*y))` (14 operations), and the version replacing
the outer w on the first factor by `U(U(w))` (38 operations). Neither has a
proved unrestricted converse or a proved finite quasigroup reduction. The
normalized searches assume quasigroups and reduce to permutations a,b with
`U(x)*y=a(x*y)`, `x*a(y)=b(x*y)`, and a crossed identity using respectively
`b(y)` or `a(a(b(y)))`. Prover9 did not settle either normalized system in
180 CPU seconds. Full Mace4 searches with `U(0)≠0` exhausted orders 2–4 for
the 14-operation version and 2–3 for the 38-operation version, then timed
out at 5 and 4 respectively after 120 CPU seconds per run. These are bounded
research checks, not additional catalogue facts.

## Cyclic restrictions and three division-only criteria (4 November 2026)

**No additional unrestricted single-equation row closes here.**
[`CyclicImageShape.lean`](../equational_theories/Parastrophes/CyclicImageShape.lean)
generalizes the earlier E872 obstruction. Constant magmas force a prospective
defining equation to have a variable on one side. Right projection fixes the
rightmost variable; cyclic unary operations determine the right-branch depth;
left projection excludes the same variable at the leftmost leaf. For E1312,
the resulting shape is exactly `x=A*(B*x)`, up to exchanging the equation's
sides, with A's leftmost variable different from x.

[`Equation1312Image.lean`](../equational_theories/Parastrophes/Equation1312Image.lean)
also proves that multiplication and its left division have the same squares,
that their right translations commute, and that division preserves a product
when both inputs are right-translated by that product. These necessary laws
are weaker than the following exact criterion. In each row below, **assume D
has bijective rows**, and write `*` for D. Then D is in the indicated
left-division image if and only if the displayed condition holds:

| Source | Exact condition in division notation |
| --- | --- |
| E1312 | `a*b=b*c` implies `c*(a*(a*b))=a*b` |
| E1112 | `x*(y*z)=y` implies `z*(y*x)=x` |
| E1315 | `(a*b)*a = b*((a*b)*((a*b)*a))` |

All three equivalences hold on arbitrary carriers and are checked in Lean.
The E1312 condition follows a three-step chain of original right translations.
The E1112 hypothesis identifies z as the original product `y*(x*y)`.
For E1315, set `y=a*b` and `x=y*a` in division notation; the original products
are then `y*x=a` and `a*y=b`, so two cancellations translate the original
law into the displayed equation. The latter has seven operations and canonical
extended number **E13834319**. Its constant-operation counterexample is also
proved: the left-bijectivity condition cannot be omitted.

The companion modules are
[`Equation1112ImageCriterion.lean`](../equational_theories/Parastrophes/Equation1112ImageCriterion.lean)
and
[`Equation1315ImageCriterion.lean`](../equational_theories/Parastrophes/Equation1315ImageCriterion.lean).
No characterization attribute is attached: two conditions are quasiidentities,
and all three retain a bijectivity hypothesis.

The [shape-search record](../data/parastrophes/image_shape_search_20261104.json)
stores bounded E1312/E1112/E1315 candidate searches and counterexamples, plus
unsuccessful positive-matrix searches. Those are research computations, not
Lean nonexistence results. A subsequent E1315 search on 67 source models
reached three million distinct value signatures, fully generating subterms
through eight operations and part of the ninth layer. It found no two-variable
candidate `x=A*(B*x)` with A's leftmost variable y. This does not exclude longer
formulas or settle the characterization question.

## E477: strengthening the inverse-core sample pool (4 November 2026)

The finite image criterion is still E411 + E4332 together with injectivity of
`c(x)=x*(x*x)`. A search for a uniform inverse of c produced fifteen successive
candidate terms, with 8–26 operations. Mace4 refuted every one using a source
model of order 5–10. The final search reached 1.5 million value signatures;
its candidate, too, is refuted. None is an unrestricted negative result about
inverse terms or single-equation characterizations.

The [data](../data/parastrophes/e477_core_inverse_candidates_20261104.json)
contains all fifteen terms and source tables, plus five specializations of the
already Lean-proved translation family. These source tables now feed the
existing term-search loader, so it will not rediscover the same false formulas.
[`check_parastrophe_e477_core_inverse.py`](../scripts/check_parastrophe_e477_core_inverse.py)
independently verifies every source law, constructs each actual division,
checks that c is a permutation, and replays each failed inverse evaluation.
These new finite examples are Python-checked research data; they have not been
promoted to Lean catalogue facts.

## E477: one unary map controls both division sides (5 November 2026)

**The unrestricted single-equation question remains open.**
[`Equation477Core.lean`](../equational_theories/Parastrophes/Equation477Core.lean)
sharpens the existing two-equation criterion. Assume E411 + E4332 and put
`c(x)=x*(x*x)`. On arbitrary carriers, the following three conditions are
equivalent: c is injective; every row is injective; every column is injective.
The analogous three surjectivity conditions are also equivalent. Thus the
left-division image of E477 is exactly this pair of identities together with
**bijectivity of c**, without a finiteness assumption. This retains that
condition explicitly; it does not replace it by an equation.

Crossing gives `x*(y*x)=c(y)`, which transfers collisions between c, rows,
and columns. For surjectivity, the previously proved local right identity
`v=x*c(x)` satisfies `x*v=x`. A preimage `a*x=v` in the x-column then gives
`c(a)=x*(a*x)=x`. The other implications use the crossed identities directly.

The c-fixed elements form a submagma satisfying **E14**,
`x=y*(x*y)`, and this submagma is itself a genuine E477 division image and a
quasigroup. It is nonempty whenever the original carrier is nonempty, because
`x*c(x)` is fixed by c. In an actual division image, that element is precisely
the square of x in the original multiplication. These results are all proved
in Lean, with no admitted obligations; the module built in about three seconds.

A separate scan tested the 24 remaining selected source/side targets against
the twelve explicitly registered long characterizations and their opposites.
All **576** proposed matches have finite counterexamples. The compact
[record](../data/parastrophes/existing_long_targets_20261105.json) shares 66
source tables, and
[`check_parastrophe_existing_long_targets.py`](../scripts/check_parastrophe_existing_long_targets.py)
replays every exclusion using the original source laws and inverse operations.
This excludes those existing formulas, not all possible defining equations.

Two bounded Prover9 runs also investigated whether cancellation yields an
additional pure identity separating the known six-element nonimage from
E477's image. The runs used either both division operations or an inverse
of c. Their pure consequences (6 and 189 distinct identities respectively)
all held in that nonimage. Each run stopped at its 180-CPU-second limit.
This is evidence about those searches only: no completeness or equality of
equational theories has been established.

## E481 and E477: an infinite obstruction to every image axiom set (5 November)

The arbitrary-carrier left-division images of **E481 and E477 are not
characterized by any set of magma equations**. This is stronger than excluding
one equation. The new connection and its proof are in
[`Equation481InfiniteImage.lean`](../equational_theories/Parastrophes/Equation481InfiniteImage.lean).
Both negative single-equation facts have catalogue attributes and export with
Lean source references. They concern actual images of source models admitting
division; they do not give division to every source model.

The proof reuses the countable twisted-cycle quasigroup previously constructed
for E1496. Write D for its multiplication and e for its right identity. It
satisfies `D(x,D(y,x))=C(y)`, where C shifts the integer height up by one, and
`D(e,y)=C(y)`. Its left division M has constant square e. The existing
right-unital crossed translation theorem therefore proves **E481 for M**;
specialization gives E477. Elements of nonnegative height, together with e,
form a D-submagma. Its e-row misses height zero. Every magma identity of the
full image descends to this submagma, whereas membership in either actual
image requires bijective rows. This excludes an arbitrary axiom set.

There is also a direct answer to the **arbitrary-carrier** inverse-core search.
For this one fixed D, `c(x)=D(x,D(x,x))` is C. Every unary D-term evaluated at a
height-zero generator stays at nonnegative height, so applying c to it cannot
return that generator. Thus no unary term inverts c, and no binary term even
chosen specifically for this D recovers its left division. The module proves
both claims and the resulting failures of uniform inverse-core recovery over
all E481 images and over all E477 images. These statements concern recovery
*from the image operation*, not the catalogue's forward division terms in the
original source operation.

**Neither finite single-equation question is settled by this argument.**
The relevant arbitrary-source sides were already marked inapplicable in the
main table, so these new conditional-image negatives do not reduce its
remaining finite gap count. The countable example does not prove that a
uniform inverse term fails on finite images. Such a transfer would need a
separate finite approximation argument; no such argument is claimed here.
All new proofs are checked in Lean, using only its usual logical axioms and
no admitted obligations or native checks.

The accompanying [finite search record](../data/parastrophes/e477_core_inverse_candidates_20261105.json)
saves four further E477 source models, of orders 8 or 9, refuting inverse-core
terms with 26, 28, 28, and 30 operations. The existing independent checker now
replays both dated files (19 refutations altogether). A fifth search reached
12 million distinct value signatures, with subterm layers through 15 complete
and layer 16 partial; it was stopped during the final candidate lookup.
These are Python-checked finite research data, not additional Lean catalogue
claims or a proof excluding every finite inverse term.

## E917: comparison identities and a central-extension converse (5 November)

**The unrestricted single-equation row remains open.** There is now a converse
theorem covering arbitrary finite central extensions, rather than just affine
operations or a finite collection of offset searches. Write
`q(x)=(x*(x*x))*x`, `U(x)=x*q(x)`, and `H(x,y)=q(x)*(x*y)`. The candidate is

```
x = ((U(w)*(y*z))*v) * H(x,U(w*(y*U(z)))*v).
```

It has **48 operations and five variables**. In particular, expanding `U(t)`
duplicates t five times; treating U as one extra operation would undercount
the formula. Its syntax and operation count are checked in
[`Equation917CancelComparison.lean`](../equational_theories/Parastrophes/Equation917CancelComparison.lean).
Every actual E917 left image satisfies it. Conversely, the candidate forces
surjective rows on arbitrary carriers, and a quasigroup and bijective U on
finite carriers. It has an exact reduction to three permutations d,g,c:

```
x*U(y) = d(x*y)              U(x)*y = g(U(x*d(y)))
g(x)*y = c(x*y)              c(y)*H(x,y) = x.
```

The output maps c,d commute. Every U-cycle has the same length, and one fixed
point would prove the full converse. No existence of that fixed point is
claimed. These facts are Lean theorems and justify the normalized searches.

[`Equation917CentralShifts.lean`](../equational_theories/Parastrophes/Equation917CentralShifts.lean)
proves the converse on every finite operation

```
(i,s)*(j,t) = (B(i,j), a*s+b*t+phi(i,j)),
```

where B is any genuine E917 left image, the fibre is any finite commutative
ring, and phi is any offset table. The coefficients are initially arbitrary;
on a nonempty carrier the candidate forces their invertibility. The proof also shows that this
converse is preserved when another such extension layer is added. Thus an
arbitrarily tall tower starting with the one-element magma cannot refute this
candidate. B need not be affine or commutative, and the offsets need not have
any special form. This does **not** assert that all finite magmas are central
extensions of this kind.

The proof uses the natural shifts of the fibres. A single point where U stays
in its own fibre makes U a uniform shift, because `x*U(y)=d(x*y)` and an onto
column determine d everywhere. Parameter shifts give `a=-b^3` and
`h=b^6+b^5+b^3+1=0`. The candidate's two compared trees differ by the negative
of the U-shift. Two evaluations of `q(q(x))`, followed by row and column
cancellation, show that the U-displacement u also satisfies
`(b^3+b^2+1)*u=0`. The integral identity
`h-b^3*(b^3+b^2+1)=1` forces u=0, in every characteristic. All of this is
checked symbolically in Lean, without finite tables or admitted obligations.

The accompanying [search record](../data/parastrophes/e917_cancel_comparison_20261105.json)
rules out counterexamples through order **9** by external SAT checks, using
all possible nontrivial uniform U-cycle lengths. At order nine, taking
lexicographic representatives under generators of the centralizer of U made
both searches finish: approximately 24 seconds for period 3 and 61 seconds
for period 9. The earlier runs without this symmetry reduction timed out.
These UNSAT computations have not been formalized in Lean. The
[`searcher`](../scripts/parastrophe_e917_cancel_search.py) independently checks
any positive answer against the literal five-variable identity. The separate
[`encoder check`](../scripts/check_parastrophe_e917_cancel_encoder.py) compares
the encoding with that literal identity on all 590 Latin squares of orders
2–4, including 45 positive examples. It also checks that canonical orbit
representatives survive the symmetry constraints. The searches can be
reproduced with `--symmetry --orders 9 --seconds 120`.

A second, 26-operation candidate is recorded in
[`Equation917BalancedComparison.lean`](../equational_theories/Parastrophes/Equation917BalancedComparison.lean):
`x=(((U(w)*U(z))*(U(y)*t))*v)*H(x,((w*z)*(y*t))*v)`.
Its finite quasigroup/permutation reduction and constant U-cycle lengths are
also proved. It survived a bounded scan of 780 scalar offset spaces over
20 saved image bases and primes through 53; its general converse remains
open. The central-extension theorem above concerns the **48-operation**
candidate, not this other formula. No characterization attributes or new
catalogue row closures are registered in this pass.

The full parastrophe build passes. The new theorems use only Lean's standard
logical axioms; the operation-count theorem uses none. No deployment data has
been regenerated for these conditional results.

## E917: a shorter comparison and fixed-point obstructions (5 November)

**No additional single-equation row is closed here.** A new 22-operation,
four-variable candidate has an exact finite reduction to just two
permutations. With the same q, U, H as above, put `F(x,y)=y*H(x,y)`:

```
x = (U(y)*v) * H(x,F(y*v,z)).
```

[`Equation917FrontProduct.lean`](../equational_theories/Parastrophes/Equation917FrontProduct.lean)
checks its syntax, operation count, forward implication from actual images,
and the following exact finite reduction:

```
F(x,y) = a(x)
U(x)*y = b(x*y)
a(x)*y = a(b(x)*y).
```

Here a and b are permutations. There is no assumed quasigroup structure:
the candidate supplies an onto row at U²(o), and its values then supply every
row index. Finite row cancellation makes F independent of its second
argument. Comparing two instances of the candidate makes the common map a
injective; its resulting surjectivity supplies column cancellation too.

All cycles of U have the same length. A single fixed point of **any of U,
a or b** forces the whole image basis. The nontrivial algebraic step is
short enough to write out: when U=id, b=id and a shifts the first input
by a and the second input by a⁻¹. Comparing two crossed evaluations gives
`q(q(x))=a⁻²(x*x)`. Evaluating U at q(x), and then F at `(x,x)`, gives
`a²(x)=a(x)`, hence a=id. These are Lean proofs; the existence of a fixed
point in every finite model of the candidate remains unproved.

There is also a uniform parity restriction. The last displayed relation
makes b a commutator of a and a column permutation; the middle relation
makes U conjugate to b. Thus **U is an even permutation**, as proved by
`unit_even`. In particular, a single even-length U-cycle is impossible,
independently of its length.

The [bounded search record](../data/parastrophes/e917_front_product_20261105.json)
excludes counterexamples through order **9** by external SAT. Initial order-9
runs timed out; adding the proved absence of fixed points of a and b made
the period-3 and period-9 cases finish in approximately 57 and 135 seconds. A separate scalar
affine scan found no counterexample over Z/n for 2≤n≤99, including constant
offsets. Neither computation is a general converse or a Lean nonexistence
proof. The [encoder checker](../scripts/check_parastrophe_e917_front_encoder.py)
compares the literal four-variable equation with its SAT encoding on all
590 Latin squares of orders 2–4, including 45 positive examples, and checks
canonical representatives for the symmetry constraints. The
[searcher](../scripts/parastrophe_e917_front_search.py) independently verifies
any positive answer against the literal identity.

For the earlier **48-operation** candidate,
[`Equation917CancelObstructions.lean`](../equational_theories/Parastrophes/Equation917CancelObstructions.lean)
additionally proves that fixed points of d, g or c also force the image basis.
Its search record now excludes the order-10 period-2 case; periods 5 and 10
remain search timeouts. These results concern that earlier candidate, not the
22-operation formula. Both modules are imported by the parastrophe aggregate.
The full Lean build and axiom audit pass, using only the usual logical axioms
and no admitted obligations. No characterization attributes or changed
catalogue counts are attached to these still-incomplete converses.

## E917: the converse survives every extension with fibres of size at most three

The **22-operation** comparison now has a converse for a larger, purely
structural class. Suppose a finite magma D satisfies that comparison and has
a homomorphism to a genuine E917 left-division image B. If each fibre has at
most three elements, D is a genuine image too. The map need not be onto, and
there is no affine, commutativity, or coordinate assumption on the fibres.
The theorem can be applied successively along any tower of such extensions.
It concerns the 22-operation candidate, not the earlier 48-operation one.

The proof is in
[`Equation917ThreeFibres.lean`](../equational_theories/Parastrophes/Equation917ThreeFibres.lean),
with the exact conditional equivalence `FrontProduct.small_fibres_characterizes`.
In a counterexample, the already constructed permutations a,b preserve each
fibre and have no fixed points. The comparison also forces b(x)≠a(x), so
x,a(x),b(x) exhaust a fibre of size at most three. Injectivity forces b=a²
and a³=id. Substituting into the comparison gives U=a and
`(a(x))*y=a⁻¹(x*y)`.

The remaining algebra does not use finiteness. Two inverse-translation
calculations give `q(a(q(x)))=x*x` and `q(a⁻¹(x))=a(q(x))`. These imply both
`x*a(x)=q(q(x))` and `x*a⁻¹(x)=q(q(x))`. Row cancellation gives a²=id,
which together with a³=id makes a=id, contradicting the absence of fixed
points. This is a handwritten Lean proof, with no finite tables, SAT
certificates, admitted obligations, or native checks.

**The unrestricted single-equation row remains open.** This does not assert
that every finite candidate has such a quotient. No new characterization
attribute or catalogue-count reduction is claimed.

The full parastrophe build passes. The axiom audit reports only Lean's usual
logical axioms; the algebraic lemma needs `Classical.choice` and `Quot.sound`,
and the finite-fibre theorem also uses `propext`.

### E680: a new recovery counterexample

A fresh search found an eleven-operation candidate for recovering the source
multiplication from left division. Mace4 produced a nine-element E680 source
refuting it at `(0,0)`: the candidate returns 1, whereas multiplication returns
2. The source table and candidate are saved in
[`image_candidate_refutations_20261105.json`](../data/parastrophes/image_candidate_refutations_20261105.json).
The shared candidate checker independently verifies the law, division, and
failed evaluation; the standard sample loader now includes this source.
A subsequent search reached two million distinct value signatures, completing
subterm layers through eight operations and part of layer nine, without
another candidate. This is bounded research, not a negative answer about all
recovery terms or single-equation characterizations.

## E680: an exact image criterion and inverse source cubes

[`Equation680Image.lean`](../equational_theories/Parastrophes/Equation680Image.lean)
now proves the following criterion on **arbitrary carriers**. Write `*` for
D and put `c(x)=x*(x*x)`. Then D is an actual E680 left-division image exactly
when

```
x*(y*x) = c(y)
x*c(x) = c(x)*x
c is bijective.
```

The crossed identity makes c an endomorphism, and bijectivity of c supplies
both quasigroup divisions. In an actual image, c is the **source's right
cube** `(x*x)*x`, and its inverse is the **source's left cube** `x*(x*x)`.
These statements use the source multiplication, not D. The mutual-inverse
calculation is the axiom-free theorem `source_cubes_inverse`; the image
criterion uses only the usual Lean logical axioms. On finite carriers,
bijectivity in the criterion can be replaced by injectivity.

The diagonal commutation is what translates back to E680. If M is inverse
to D row by row, crossing gives `M(x,c(y))=D(y,x)`. Writing an arbitrary
argument as c(y), the commutation identifies `M(M(x,x),x)` with c(x), and
E680 follows by cancellation. This is a small algebraic proof, without
finite tables or solver certificates. **The bijectivity condition remains
explicit, so this does not close a single-equation row.**

## E917: a fourth-order permutation obstruction

The **22-operation** comparison has a further conditional converse in
[`Equation917FourthOrder.lean`](../equational_theories/Parastrophes/Equation917FourthOrder.lean).
In its established normalized form, if `b=a²` and `a⁴=id`, then the magma is
a genuine E917 left image. This concerns the auxiliary permutations on the
whole carrier. It does **not** assert that every four-element fibre has this
form, nor that the unrestricted converse is proved.

The algebraic lemma `crossed_four` works even on infinite carriers. The
hypotheses give `F(x,y)=a(x)`, `U(x)=a²(x)`, and
`(a(x))*y=a⁻¹(x*y)`. Put b=a². First q(bx)=q(x); two crossed evaluations
in a common column then give q(ax)=b(qx). These make b, then a, commute
with every row. Comparing two crossed products with the same last factor
gives `q(q(x))=x*x`. Finally the crossed identity at `(x,x)` reduces to
a(x)=a⁴(x)=x. This handwritten Lean proof replaces the exploratory
Prover9 derivation and needs only `Quot.sound`.

The full parastrophe build passes (3,789 jobs); the two new modules build in
about 2.4 and 4.7 seconds respectively. The axiom audit passes, with no
admitted obligations or native checks. The composition audit found no missed
single-equation row closure. **Catalogue counts remain unchanged**, and these
conditional results have no characterization attributes or new website
proof statuses.

## E917: double crossing and an involution quotient (5 November 2026)

**No additional single-equation row is closed.** There is a new conditional
converse for the **22-operation** FrontProduct comparison in
[`Equation917InvolutiveUnit.lean`](../equational_theories/Parastrophes/Equation917InvolutiveUnit.lean).
In its normalized form, assume `U=b`, `b²=id`, and that a commutes with b.
Then the full image basis follows, for every finite carrier. First
`q(b(x))=q(x)`; crossing transports b through the second argument as well as
the first. Its orbits therefore form a magma congruence. The quotient still
satisfies the comparison, but its U is the identity, so the existing
fixed-point converse applies there. Consequently a(x) lies in `{x,b(x)}`.
Either alternative gives a fixed point of a upstairs and finishes the proof.
There is no restriction to affine operations or to small carriers. The
hypotheses are explicit: this does not settle the other involution cases.

A **different, 72-operation** candidate is now reduced in Lean to two
permutations in
[`Equation917FrontSquare.lean`](../equational_theories/Parastrophes/Equation917FrontSquare.lean).
With `q(x)=(x*(x*x))*x`, `U(x)=x*q(x)`, `H(x,y)=q(x)*(x*y)`, and
`F(x,y)=y*H(x,y)`, its formula and exact finite normalized form are

```
x = (U(y)*v) * H(x,F(F(y*v,z),w))

F(x,y) = a(x)
U(x)*y = b(x*y)
a(a(x))*y = a(b(x)*y).
```

The candidate forces a quasigroup; both a and b are permutations. Initially
cancellation only makes the double composite F(F(x,z),w) independent of z,w.
One of its values supplies a bijective H-column. The corresponding F-column
then cancels the composite, making F itself common. A fixed point of a forces
the full image basis. Both a and U have uniform cycle lengths, but a fixed
point of U alone has **not** been proved sufficient for this candidate.

The [research record](../data/parastrophes/e917_front_square_20261105.json)
excludes counterexamples to the 72-operation formula through order eight by
external SAT. At order nine only the U=id case is excluded; the period-three
and period-nine searches timed out, including runs using the proved uniform
cycles of a. The
[encoder checker](../scripts/check_parastrophe_e917_front_square_encoder.py)
compares the literal identity with the normalized encoder on all 590 Latin
squares of orders 2–4, including 45 positive tables. These are external
research checks, not Lean nonexistence proofs.

Two additional block searches concern the **22-operation** formula: four-point
fibres over the order-three subtraction magma, and over the saved idempotent-free
order-five image. Both exclude counterexamples with U and a involutions, in
about 1.3 and 15.7 seconds respectively. Multiplication inside the blocks was
unrestricted subject to the quotient and normalized equations; no fixed affine
coefficients were imposed. These are restricted extension searches, **not**
exclusions of all counterexamples at orders 12 and 20. Prover9 and Vampire
attempts at the general converses timed out without proofs.

Finally, for the shorter candidate `x=U(y)*H(x,F(y,z))`,
[`Equation917ShortFront.lean`](../equational_theories/Parastrophes/Equation917ShortFront.lean)
proves that every finite model has all columns `x ↦ H(x,c)` bijective.
The good column indices include every F(y,z) and are closed under their own
D-rows. A bijective unit row inside that set then covers all indices.
One injective H-row would suffice to make all D-rows bijective, but existence
of that row and the full converse remain open.

All three modules are imported by the parastrophe aggregate. The full build
passes (3,792 jobs); each new module builds in approximately five seconds.
The axiom audit uses only Lean's usual logical axioms, with no admitted
obligations, native checks, or external proof certificates. No characterization
attributes, catalogue counts, or website proof statuses have changed.

## E917: a regular-output converse and much smaller searches (5 November 2026)

**The unrestricted single-equation row is still open.** For the 22-operation
FrontProduct candidate, the normalized equations are

```
F(x,y)=a(x),    U(x)*y=b(x*y),    a(x)*y=a(b(x)*y).
```

[`Equation917RegularOutput.lean`](../equational_theories/Parastrophes/Equation917RegularOutput.lean)
proves that **U=b alone finishes the converse**. The algebraic theorem
`basis_of_regular_unit` works on arbitrary quasigroups: neither finiteness,
commutation of a and b, nor any bound on their orders is assumed. A left-division
comparison first forces ab=ba. Transporting these permutations through both
arguments then gives `q(bx)=q(x)`, `q(ax)=b(qx)`, and
`q(q(x))=a⁻²b³(x*x)`. Apply the unit equation at q(x), then crossing at (x,x),
to obtain ab=id. The first-argument shift now forces a=id and b=id. This
handwritten proof subsumes the earlier finite involution case; it uses no
finite tables or solver certificates.

Within finite models of the candidate, the full image basis is now equivalent
to either `U(x*y)=U(x)*y` for every x,y, or simply **`q(U(x))=q(x)` for every
x**. These are proved equivalences, not proved consequences of the candidate.
In particular a counterexample must have a concrete core defect somewhere.
The more general Prover9 attempts, including one with a involutive, still
ended at their time limits without proofs.

A second new module,
[`Equation917OutputWords.lean`](../equational_theories/Parastrophes/Equation917OutputWords.lean),
organizes the auxiliary permutations as a group. Outputs of left-index
autotopies act freely: two output maps agreeing at one point agree everywhere.
This applies to **mixed words** in a,b, not merely to their separate powers.
The group generated by a,b has order dividing the carrier size, proved in
`generated_outputs_card_dvd`. These restrictions substantially reduce the
small counterexample searches.

At orders nine, ten, and eleven the search reduces to eleven, nine, and nine
normal forms respectively. All 29 forms are UNSAT in external SAT searches.
Their slowest checks took about 1.2, 6.5, and 1 second respectively, including
encoding. The older order-nine and order-ten timeouts
therefore no longer leave those sizes unresolved **for counterexamples to this
candidate**. This is not a nonexistence claim about E917 magmas of those orders.
Together with the earlier small searches, the candidate has survived through
order eleven. The permutation enumeration and SAT exclusions are **not Lean
nonexistence proofs** and add no catalogue characterization attributes.

The records contain the actual permutations, solver statistics, and proof-status
boundary:
[order nine](../data/parastrophes/e917_output_groups_order9_20261105.json),
[order ten](../data/parastrophes/e917_output_groups_order10_20261105.json), and
[order eleven](../data/parastrophes/e917_output_groups_order11_20261105.json).
The [fixed-output search](../scripts/parastrophe_e917_output_group_search.py)
replays these cases; it verifies that relabelings preserving a,b can move any
core defect to zero. The [encoder checker](../scripts/check_parastrophe_e917_output_group_encoder.py)
compares it with the literal four-variable identity on all 590 Latin squares
of orders 2–4, with 120 SAT comparisons and 45 literal positives, plus 157 checks with a
fixed unit (including deliberately incorrect units).
[`enumerate_parastrophe_e917_output_groups.cpp`](../scripts/enumerate_parastrophe_e917_output_groups.cpp)
enumerates every possible a for the permitted uniform b permutations and
checks freeness at every point. An additional
[order-ten enumeration](../scripts/check_parastrophe_e917_order10_groups.cpp)
checks the nine cyclic/dihedral normal forms independently: 3,628,800
permutations, 33 free generating pairs, no unmatched forms.

The full parastrophe build passes (3,794 jobs). The new Lean proofs use only
its usual logical axioms, with no admitted obligations or native checks.
Catalogue counts remain unchanged: **39 finite image gaps per side and 4,628
fully settled finite rows**. No deployment bundle was regenerated.

At order eleven, the free output group has order dividing eleven and contains
nonidentity b, so b generates that whole cyclic group. Normalize b to successor;
then a=b²,...,b¹⁰ are all possibilities. The smallest unresolved counterexample
order for the 22-operation candidate is therefore now **twelve**, not nine.

Order **twelve** is now excluded externally as well. Of its 35 output-pair
forms, 34 are UNSAT directly. The last one has a Klein-four output group.
The new Lean lemma `unit_partner_relations` forces U to be an involution
commuting with c=a∘b⁻¹, with U(x) neither x nor c(x). Pairing the six c-orbits
and choosing the orientations gives exactly 120 possible U permutations.
The 384 relabelings preserving a,b reduce these to ten forms, all UNSAT in
2.4–7.6 seconds. **For these refinements U is fixed globally; no core defect
is also imposed at zero**, since the smaller symmetry group need not move
all points to zero.

The [order-twelve record](../data/parastrophes/e917_output_groups_order12_20261105.json)
preserves the unrefined Klein-four timeout and points to its
[ten completed refinements](../data/parastrophes/e917_output_groups_order12_v4_20261105.json).
The slowest directly completed form took about 168 seconds; the dihedral
order-twelve form took about 93 seconds. The
[normal-form generator](../scripts/generate_parastrophe_e917_order12_groups.py)
reproduces both the 35 pairs and the ten refinements. The abstract finite-group
classification and the SAT results remain external research, whereas the
free-action, divisibility, and unit-partner reductions are checked in Lean.
Thus **thirteen is now the smallest unchecked counterexample order** for this
candidate. This still does not close its unrestricted characterization row.

## E910: the finite and arbitrary image questions are closed negatively (5 November 2026)

**No single magma equation characterizes E910's left-division image, even
among finite magmas. In fact no set of magma equations does.** The new proof
is in
[`Equation910SingularImage.lean`](../equational_theories/Parastrophes/Equation910SingularImage.lean),
with registered results `Catalogue.left_noSingleEquation910_fin` and
`Catalogue.left_noSingleEquation910_all`. Duality closes E2737's right image.
This supersedes the open status in the earlier E910 sections; their exact
criterion, E427 plus bijective rows, remains the starting point of the proof.

The witness is a seven-part affine operation
`D((i,u),(j,v))=(colour(i,j),A(i,j)*u+B(i,j)*v)` with integer coefficients.
Every base row is a permutation. The B coefficients are ±1 except for a
single -2, and a 49-case integer coefficient certificate proves E427 over
every commutative ring. Modulo each odd prime, all B coefficients are units,
so D has bijective rows and is an actual E910 left-division image. Modulo two,
its row at `(1,0)` identifies `(3,0)` and `(3,1)`. Thus this 14-element
reduction cannot be a division image.

Now let K be *any* magma equation holding in every finite E910 division image.
For every integer assignment, the difference between K's two evaluated integer
coordinates is zero modulo every odd prime, hence is zero in the integers.
Reduction modulo two then transfers K to that same 14-element nonimage.
Consequently the nonimage satisfies **every equation** shared by the finite
images, ruling out an equational characterization of any size. This unbounded
transfer argument is the Lean theorem `Eq910SingularImage.bad_inherits`; it
is not a bounded enumeration of proposed defining equations.

Allowing zero left coefficients in the affine search produced the obstruction.
The [saved construction](../data/parastrophes/e910_singular_image_20261105.json)
contains all integer coefficients and the collision. The
[search script](../scripts/parastrophe_e910_singular_bundle.py) uses signed
monomials in an indeterminate; the final Lean proof checks the specialized
integer matrices independently. The
[independent checker](../scripts/check_parastrophe_e910_singular_bundle.py)
checks the 49 exact coefficient identities, the bad reduction, and the actual
inverse-source laws at orders 21, 35, and 49. Lean proves the odd-prime family
uniformly. No SAT/SMT certificate, `sorry`, native evaluation, or extra axiom
is used by the proof.

After ordinary-equivalence and duality propagation, **six finite rows** close:
E504, E910, E1722, E1925, E2737, and E3143. Applicable finite image gaps fall
**39 → 36 per side**, and fully settled finite rows rise **4628 → 4634**.
For arbitrary carriers, E910 and E2737 close: image gaps fall **3 → 2 per
side**, and fully settled rows rise **4688 → 4690**. The local website
catalogue has been regenerated with Lean source references; the deployment
bundle has not been rebuilt. The full parastrophe build passes (3,795 jobs),
and the new module builds in about eight seconds. Its axiom audit uses only
Lean's usual `propext`, `Classical.choice`, and `Quot.sound`.

## E477 and E680: two more finite image questions closed negatively (5 November 2026)

**Neither E477 nor E680 has an equationally characterizable left-division
image, even among finite magmas.** The new proofs are in
[`CrossedSingularImages.lean`](../equational_theories/Parastrophes/CrossedSingularImages.lean).
The registered finite results are `Catalogue.left_noSingleEquation477_fin`
and `Catalogue.left_noSingleEquation680_fin`. This supersedes the finite
single-equation gaps in the earlier sections. Their conditional image
criteria remain useful and are exactly what the proof uses.

Both constructions have only three parts. Their common base operation is
`i*j = 1-i-j` modulo three, with a ring coordinate attached to each part.
Multiplication has the form `D((i,u),(j,v))=(i*j,A(i,j)*u+B(i,j)*v)`.
For both coefficient tables the crossed cubic map is simply
`c(i,u)=(i,2*u)`, and `x*(y*x)=c(y)`. The E477 family also satisfies
`x*(x*c(x))=x`; the E680 family satisfies `x*c(x)=c(x)*x`. Nine integer
coefficient checks prove the crossed identity over every commutative ring,
and three more checks prove the corresponding diagonal identity.

Modulo every odd prime, doubling is injective and the exact image criteria
therefore give genuine division images. Modulo two, each family is a
six-element nonimage with an explicit row collision. Every equation valid
in all finite images holds in all the odd-prime reductions, hence over the
integers, hence in that bad six-element reduction. This rules out **every
set of magma equations**, not merely proposed equations below some search
bound. The individual `E477.bad_inherits` and `E680.bad_inherits` theorems
record this stronger statement. The proof also excludes arbitrary-carrier
characterizations; E477 already had a separate infinite obstruction.

The reusable transfer argument is in
[`PartitionedReductionImage.lean`](../equational_theories/Parastrophes/PartitionedReductionImage.lean).
The [saved coefficient tables](../data/parastrophes/crossed_singular_images_20261105.json)
have an [independent exact-arithmetic checker](../scripts/check_parastrophe_crossed_singular.py).
The [generalized search](../scripts/parastrophe_singular_bundle.py) expands
the source law after inverting each affine division row. Signed powers of
an indeterminate turn the resulting Laurent-polynomial identities into
finite cancellation constraints. It finds both three-part constructions
quickly; Lean independently checks the specialized integer data. No solver
certificate, `sorry`, or native evaluation enters the proofs.

After equivalence, duality, and the existing image-transfer rules, **sixteen
finite characterization cells** close, eight per side. Eight equation rows
become fully settled: E477, E680, E1492, E1695, E1932, E2135, E2947, and E3150.
Finite image gaps fall **36 → 28 per side**, and fully settled finite rows
rise **4634 → 4642**. Arbitrary-carrier applicable gaps remain **2 per side**,
with 4690 fully settled rows. The local catalogue has been refreshed; no
deployment archive was rebuilt. The aggregate Lean build passes (3797 jobs),
the new construction module builds in 4.3 seconds, and its axiom audit uses
only `propext`, `Classical.choice`, and `Quot.sound`.
