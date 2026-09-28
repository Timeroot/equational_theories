# Open spectrum catalogue maintenance

The website now summarizes the 17 unresolved finite-FO representatives using
proved constructions, individually classified exclusions, and concrete remaining
orders. An unknown exact spectrum no longer hides its proved partial results.

The catalogue's lower bounds now include every positive fourth power for E670,
E677, E1076, E1286, and E1313. For E467, E704, E1110, E1279, and E1516, they
include every order supplied by the idempotent E63 construction, every cube,
and all orders at least 1228. These bounds are assembled in
`Spectrum/OpenConstructions.lean` and `Spectrum/Generated/NoteBounds.lean`.
The generator also includes the existing checked modular witnesses rather than
only the historical examples transcribed from the note.

New complete Lean results:

- E677 excludes orders 3 and 4 (`Spectrum/Equation677/Small.lean`).
- E1083 excludes orders 5 and 6 (`Spectrum/Equation1083/SmallExclusions.lean`).
- E670, E1286, and E1516 have models of order 9; E1076 and E1313 have models
  of order 19; E907 has a model of order 23 (`Spectrum/OpenWitnesses.lean`).

The finite exclusions use registered native LRAT checkers. The positive
witnesses use ordinary Lean proofs. Their declarations have transitive proof
status checks. See the corresponding small-exclusion notes for certificate
sources and replay instructions.

For each unresolved law, the website's lower and upper bounds, individual
exclusions, and explicit cofinite cutoff have named Lean declarations. The
auditor checks both their types and their actual transitive dependencies.
`scripts/spectrum_overview.py` evaluates the proved lower formula and closes
the included orders under products, using `Law.MagmaLaw.HasModel.mul`.
With a proved tail the displayed gap list is exhaustive; otherwise it is
explicitly an initial segment through 64. Pending exclusions are displayed
separately and never treated as Lean-proved nonexistence.

In particular, E63 has seven unresolved existence questions and two reported
exclusions awaiting Lean replay. E1483's reported exclusion at order 11 is now
shown with its existing admitted declaration and certificate-omission note.
The general Wilson arguments remain paper results; their congruence conditions
are not presented as obstructions for arbitrary models.

The separate E677/E255 investigation proves that idempotent and scalar-affine
constructions cannot give a counterexample. See
[677_255_designs_research.md](677_255_designs_research.md).

Checks include `scripts/check_spectrum.lean`, `scripts/test_spectrum_overview.py`,
`scripts/test_spectrum_view.mjs`, and the generated research-site integration
tests. The committed website data bundle is regenerated after the source commit
so its proof links point at that exact revision.
