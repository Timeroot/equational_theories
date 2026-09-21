# Research website

The Equation Explorer (`home_page/implications/`), Graphiti (`home_page/graphiti/`),
and spectrum catalogue (`home_page/spectrum/`) share the static modules in
`home_page/research/`. They work under `/equational_theories/` or another project
prefix; their links and fetches are relative. Jekyll's `url` is the origin and
`baseurl` is the project prefix.

## Publishing

**Deploy website** (`.github/workflows/blueprint-paper.yml`) publishes pushes to
`definability-negative` and can also be run manually on that branch. GitHub Pages
must use **GitHub Actions** as its source; this fork already has that setting and
allows this branch in the `github-pages` environment.

The workflow restores `website_data/site-data.tar.gz`, checks every asset against
`website_data/manifest.json`, runs the JavaScript integration checks, builds
Jekyll, and deploys the result. It installs no Lean toolchain and performs no Lean,
LaTeX, or API-documentation build. Pull requests build and check the site without
deploying it. Proof-only pushes leave the published data unchanged. Push a refreshed bundle
to publish new mathematical results.

The archive contains the ten relation boards, proof provenance, spectrum data,
legacy explorer graphs, dashboard assets, raw-data downloads, and the generated
Finite Magma Explorer data. Pages serves ordinary extracted JSON; browsers do not
need to decompress the archive. This uses regular Git, without Git LFS. The
manifest records the source commit, generation time, file sizes, and SHA-256 hashes.

The navigation links to the original project's published blueprint, paper, and
API documentation. Fork-specific proof links point directly to this repository's
Lean declarations at the commit recorded in the data.

## Refreshing the data locally

Install Lean/Lake, Python 3, Ruby, and Node.js. Python additionally needs:

```sh
python3 -m pip install numpy pillow markdown
```

Commit the Lean and evidence changes first, so that exported source links point
to a real commit. From the repository root, run:

```sh
python3 scripts/build_website_data.py
```

This builds the project and extractor, regenerates all site data, checks compiled
Lean declaration evidence and spectrum witness types, verifies every relation
matrix against the audit, checks proof reconstruction, and packs the result.
Exports run sequentially to avoid loading multiple large Lean environments at
once. Temporary exports use the ignored `.cache/website/` directory; large raw
JSON intermediates are removed after compression.
`--skip-build` is available when the local Lean build is already current.

Then commit and push the refreshed files:

```sh
git add website_data/site-data.tar.gz website_data/manifest.json
git commit --author="Alex Meiburg <timeroot.alex@gmail.com>" -m "Refresh website data"
git push fork definability-negative
```

The deployment workflow does the rest. Website-only changes can be published
without regenerating the data. If you change the publication branch, update both
the workflow's push filter and deployment condition, and the Pages environment's
allowed branches.

`GITHUB_REPOSITORY` controls source links, defaulting to
`Timeroot/equational_theories` locally. The standalone lower-level exporter remains
`scripts/generate_research_site.py`; the build script supplies its compiled
Lean declarations and raw implication entries.

## Previewing without Lean

Restore the bundle into a copy of the site to avoid changing tracked source files:

```sh
mkdir -p .cache/site-preview
cp -R home_page/. .cache/site-preview/
python3 scripts/website_data.py unpack --site .cache/site-preview
python3 -m http.server --directory .cache/site-preview
```

This serves the standalone explorers. To preview the landing page and dashboard
with their layout, use Jekyll with `home_page/Gemfile` and the restored copy as its
source. The configured project prefix is `/equational_theories`.

The research-data generation checks:

1. The spectrum catalogue's declaration types and transitive evidence.
2. Compiled Lean declaration names, source lines, and dependency status.
3. Source-labelled relation generators and the closure of all ten relations.
4. Every positive and negative cell against `scripts/definable.py`.
5. Complete coverage by a compact set of negative witnesses.
6. Proved equivalence classes, possible merges, and spectrum data.
7. JavaScript proof reconstruction and catalogue integration.

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
