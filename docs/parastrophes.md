# Quasigroup laws and their parastrophes

The catalogue at `parastrophes/` and the Equation Explorer's property panel track
questions about the **actual left and right division operations**. These are
separate from the eight existential definability relations. An arbitrary
construction of some target magma does not identify its operation with division.

For an operation `*`, left division `x \ y` is the unique solution of `x * z = y`;
right division `x / y` is the unique solution of `z * y = x`. Together with `*`
and the opposites of these three operations, these are the six parastrophes.
Some can coincide. A quasigroup has bijective rows and columns. Empty carriers
are allowed, consistently with the rest of the project.

## Questions and quantifiers

Every numbered law has separate `all` (possibly infinite) and `fin` fields:

| Field | Lean predicate | Meaning |
|---|---|---|
| Always a quasigroup | `QuasigroupLaw scope L` | Every model of L in this scope has bijective rows and columns. |
| Left/right image characterized by one equation | `SingleEquation scope L side` | There is an identity whose complete model class is exactly this division image. |
| Left/right term per model | `TermRecovery scope L side` | For every L-model, there exists a parameter-free binary term for the specified division. |
| Left/right uniform term | `UniformTermRecovery scope L side` | There exists one binary term that works for every L-model in the scope. |

`Characterizes scope L side target` provides a specified witness for
`SingleEquation`. Its definition is an iff over **all target magmas**, so it
includes the converse and excludes extra target models that are not quasigroups.
The image consists of divisions of quasigroup L-models. In the website these
questions are used for quasigroup laws: a proved non-quasigroup counterexample
makes the division fields **Not applicable**, rather than incorrectly asserting
that all their answers are negative. A currently unknown quasigroup field is
not itself a negative.

`SingleEquation` quantifies over `Law.NatMagmaLaw`, with arbitrarily many finite
variables and operations. A negative excludes **every single identity**, not
merely the 4694 catalogue equations. Positive records can name an equation outside
the numbered catalogue; its actual syntax is exported and displayed.

Term recovery does not require a positive single-equation characterization.
`IsDivision` asserts both inverse identities. Thus a recovery term denotes the
actual division, not just an arbitrary right inverse or an operation satisfying
some target law. The terms contain no parameters or extra constants.

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
* If L forces a quasigroup on arbitrary carriers, **both divisions automatically
  have uniform terms**. Solve the division equation on the free generators and
  represent the solution by a term. Evaluation homomorphisms transfer the first
  inverse identity; cancellation gives the other one.
* If L forces a quasigroup on finite carriers, **both divisions automatically
  have a term in each model**. On a carrier of size n, every translation's inverse
  is its `(n! - 1)`st iterate. The exponent depends on n, so this does **not** prove
  uniform term recovery across all finite models.
* Conversely, terms for both divisions imply the quasigroup property. The proof
  display includes both division premises.
* An exact characterizing target law forces a quasigroup: divisions of
  quasigroups are quasigroups.

Consequently, among laws already known to force quasigroups, the genuinely
additional term question is **uniform recovery in the finite-only setting**.
The all-carrier and per-finite-model term questions are filled by these general
Lean results even when no convenient short witness has been recorded.

Ordinary implication transfers the universal quasigroup and term properties
in the appropriate direction. Exact single-equation characterization transfers
only under **ordinary implication equivalence** of source laws. The viewer uses
neither term-structural nor FO-definability equivalence for this purpose. Every
such transfer links its implication path in the ordinary graph.

Duality preserves quasigroup status but swaps left and right. More precisely,
left division of the opposite magma is the opposite of right division, so
characterization targets must also be dualized. An explicit term is transformed
by mirroring its operation tree and interchanging its two variables. A negative
transfers by the same involution.

## Registering results

Import `equational_theories.Parastrophes.Attributes` and the required source
laws/proofs. Add completed theorems with `@[parastrophe_result]`, for example:

```lean
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
For a quasigroup negative, package the concrete counterexample as a proof of
`¬ QuasigroupLaw`; the theorem's docstring should describe it.

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
  This obstruction is formalized without a model-search certificate. Its finite
  analogue is **not** asserted by this proof.
* E704, E1279 and E1313: existing finite Latin-square reductions are registered;
  the general finite theorem supplies their terms per model. Their uniform
  finite terms are not asserted by those reductions.
* E1, E3, E4, E46 and E168: small explicit non-quasigroup countermodels seed
  negatives. The E168 example is the four-element central groupoid
  `(a,b) ◇ (c,d) = (b,c)`.

These are initial integrations, not a claim to have audited every historical
parastrophic construction. In particular, a reversible pair of arbitrary terms
or a parastrophy statement conditional on being a quasigroup is insufficient
for an unconditional exact characterization record.

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
