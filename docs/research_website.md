# Research website

The Equation Explorer (`home_page/implications/`), Graphiti (`home_page/graphiti/`),
and spectrum catalogue (`home_page/spectrum/`) share the static modules in
`home_page/research/`. They work under `/equational_theories/` or another project
prefix; their links and fetches are relative. Jekyll's `url` is the origin and
`baseurl` is the project prefix.

The **Compile blueprint and paper** workflow generates their data after building
Lean. Its new research-data step:

1. Checks the spectrum catalogue's declaration types and transitive evidence.
2. Exports compiled Lean declaration names, source lines, and dependency status.
3. Collects source-labelled relation generators and closes all ten relations.
4. Compares every positive and negative cell against `scripts/definable.py`.
5. Chooses a compact set of negative witnesses and verifies full coverage.
6. Exports proved equivalence classes, their possible merges, and spectrum data.
7. Runs the JavaScript proof-reconstruction and catalogue integration checks.

Generated JSON is ignored by git. It must be built before serving the site;
GitHub's automatic branch-based `pages-build-deployment` does not generate it.
The publishing workflow's existing docgen action handles Jekyll and deployment.

To generate the research data locally after `lake build equational_theories`:

```sh
lake exe extract_implications raw --full-entries > /tmp/general-entries.json
lake exe extract_implications raw --full-entries --finite-only > /tmp/finite-entries.json
lake env lean scripts/check_spectrum.lean
python3 scripts/website_declarations.py
lake env lean scripts/export_website.lean
OPENBLAS_NUM_THREADS=2 python3 scripts/generate_research_site.py \
  --declarations /tmp/website-declarations.json \
  --general-entries /tmp/general-entries.json \
  --finite-entries /tmp/finite-entries.json
lake env lean scripts/check_website_witnesses.lean
node scripts/test_research_proofs.mjs
node scripts/test_research_site.mjs
```

Python needs NumPy. The Lean exporter writes `/tmp/website-declarations.json` by
default; `WEBSITE_DECLARATIONS` overrides that path. `GITHUB_REPOSITORY` controls
source links, defaulting to `Timeroot/equational_theories` locally. Links pin the
source commit recorded when generating the data.

The new standalone explorers can be previewed with `python3 -m http.server
--directory home_page`. Building the landing page and layout also needs the
existing Jekyll dependencies. The former explorers remain as `legacy.html` in
their respective directories and use the pre-existing data-generation steps.

## Evidence contract

Relation statuses are `0` unknown, `1` proved yes, `2` proved no, `3` conjectural
yes, and `4` conjectural no. The last two occur only for implication. Classes use
only status `1` in both directions. Distinct classes remain possibly equivalent
until at least one direction has status `2`; a speculative negative does not
settle the classification.

Source-labelled positive generators reconstruct paths. For a negative queried
at a stronger relation, the viewer reconstructs paths in the original witness's
relation, then uses contraposition of the hierarchy. This distinction matters:
a path in FO definability must not be presented as a term structural proof.
Family obstructions cite the obstruction lemma, a satisfied-law certificate,
and the family refutation certificate.

Spectrum `PROVED` means completed Lean evidence; `PROOF_AVAILABLE` and `NOTE_GAP`
are conjectural with distinct descriptions. An exact spectrum with no purported
proof is unknown, even if someone has proposed a formula. Exactness, lower and
upper bounds, individual witnesses, and cofiniteness are labelled independently.
Native computation uses Lean's existing native-computation trust boundary.
