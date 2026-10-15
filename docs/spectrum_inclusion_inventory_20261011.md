# Open spectrum inclusions, 2026-10-11

Updated after the small-order search campaign. An arrow `A → B` means `Spec(A) ⊆ Spec(B)`. There are **55 unresolved directed arrows** between **31 known spectrum classes**, down from 64. The only possible remaining class equality is E1483/E1485; E1485 → E1483 is proved, and the reverse is open.

The nine newly refuted arrows all target E1110: their sources are E167, E467, E677, E704, E1076, E1286, E1313, E1486, and E1516. They have order-13 models, whereas E1110 now has a Lean exclusion at 13. Its new order-12 exclusion independently separates E167. E63 at 14, E1076 at 9 and 11, and E467/E704/E1076/E1279/E1483/E1516 at 12 are also now excluded in Lean.

## How to read the orders

These are the smallest possible counterexample orders given the recorded evidence, not claims that such counterexamples exist. To refute A → B at n, A must have an n-element model and B must have none. One finite order does not generally prove an inclusion.

- **+**: only the source model is missing; the target is excluded.
- **−**: only the target exclusion is missing; the source model is proved.
- **?**: both sides are unresolved.
- Every displayed order uses completed Lean proofs, including the newly formalized exclusions of E467, E1076, and E1483 at 12.

## Full inventory

| Source | Target | Earliest possible separator | Earliest positive-only opportunity |
| --- | --- | --- | --- |
| E168 | E670 | 49− | — |
| E467 | E63 | 14+ | 14+ |
| E467 | E667 | 15? | — |
| E467 | E1516 | 14? | — |
| E670 | E63 | 10+ | 10+ |
| E670 | E667 | 12+ | 12+ |
| E670 | E1110 | 10+ | 10+ |
| E677 | E63 | 10+ | 10+ |
| E677 | E667 | 12+ | 12+ |
| E677 | E1516 | 10+ | 10+ |
| E704 | E63 | 14+ | 14+ |
| E704 | E467 | 14? | 16+ |
| E704 | E667 | 15? | — |
| E704 | E883 | 15? | — |
| E704 | E1516 | 14? | — |
| E883 | E667 | 12+ | 12+ |
| E907 | E63 | 14+ | 14+ |
| E907 | E1083 | 14? | — |
| E1076 | E63 | 14+ | 14+ |
| E1076 | E667 | 15? | — |
| E1076 | E670 | 13− | — |
| E1076 | E677 | 14? | — |
| E1076 | E704 | 14? | — |
| E1076 | E883 | 15? | — |
| E1076 | E1313 | 14? | — |
| E1076 | E1516 | 14? | — |
| E1083 | E63 | 14+ | 14+ |
| E1110 | E63 | 14+ | 14+ |
| E1110 | E667 | 15? | — |
| E1279 | E63 | 14+ | 14+ |
| E1279 | E467 | 14? | 16+ |
| E1279 | E667 | 15? | — |
| E1279 | E704 | 14? | — |
| E1279 | E883 | 15? | — |
| E1279 | E1110 | 14? | — |
| E1279 | E1516 | 14? | — |
| E1286 | E63 | 14+ | 14+ |
| E1286 | E667 | 12+ | 12+ |
| E1286 | E677 | 12? | — |
| E1286 | E907 | 12? | — |
| E1286 | E1083 | 14? | — |
| E1286 | E1516 | 12+ | 12+ |
| E1313 | E63 | 14+ | 14+ |
| E1313 | E667 | 12+ | 12+ |
| E1313 | E677 | 12? | — |
| E1313 | E1516 | 12+ | 12+ |
| E1483 | E546 | 14+ | 14+ |
| E1483 | E667 | 15? | — |
| E1483 | E1485 | 13+ | 13+ |
| E1486 | E63 | 14+ | 14+ |
| E1486 | E667 | 12+ | 12+ |
| E1486 | E670 | 12? | — |
| E1486 | E1083 | 14? | — |
| E1516 | E63 | 14+ | 14+ |
| E1516 | E667 | 15? | — |

## Remaining positive targets

The still-open order-12 targets from this campaign are **E670, E677, E883, E1286, E1313, and E1486**. A positive model would separate the corresponding spectrum from E667; some would also separate it from E1110 or E1516. The bounded searches did not find models or settle these cases. The previous positive targets E1076 at 9/11 and E1110 at 12 have instead been formally excluded. E467/E1076/E1483 at 12 are also formally excluded.

Order 14 is now a positive-only opportunity for every still-open arrow into E63 whose first prospective separator is 14. The target exclusion is fully Lean-checked. E704 or E1279 at 16 would also separate the corresponding spectrum from E467. No order-ten search was undertaken in this campaign.

One finite route to proving inclusions remains finishing the E883 spectrum: models at **12, 15, 18, 39, 51, 87, 99, 153, 159, 207, 219** would fill its remaining orders by products, proving `Spec(E883) = positiveExcept {3,6,9}` and both E704 → E883 and E1279 → E883. The previous E167 → E1110 positive-completion proposal is now definitively refuted.

For a general construction, proving E670 has every square order would establish E168 → E670. The first square not currently covered is **49**. E670 has Lean cofiniteness but no explicit numerical cutoff in the catalogue.

## Evidence and scope

The pointwise audit runs through order 200,000, above every relevant Lean-formalized numerical cutoff. The minimality of the displayed small orders only uses the earlier orders. Bounds awaiting formalization are not counted as Lean evidence. Product closure and positive spectrum/finite-FO inclusions transfer positive orders forward and exclusions backward. No external-only exclusions are used in this inventory. The historical `including_external_exclusions` JSON fields are retained for compatibility and now agree with the formal columns.

[Machine-readable inventory](../data/spectrum/inclusion_inventory_20261011.json). [Search campaign and proof links](spectrum_search_campaign_20261011.md). Principal inputs are `data/spectrum/catalogue.json`, `scripts/spectrum_overview.py`, the current finite-FO relation, and `home_page/research/spectrum-relations.js`.
