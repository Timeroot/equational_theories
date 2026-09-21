# Precomputed website data

`site-data.tar.gz` contains the locally generated and verified website assets.
`manifest.json` records their source commit, relation counts, sizes, and hashes.
GitHub Pages restores this archive instead of building Lean.

Refresh with `python3 scripts/build_website_data.py` after committing proof changes.
See [the publishing instructions](../docs/research_website.md) for prerequisites,
previewing, and deployment.
