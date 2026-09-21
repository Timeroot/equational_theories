#!/usr/bin/env python3
"""Audit FO-structural equivalence gaps and conditional one-arrow impacts.

Run after definability_audit.py --write --verify-closure. By default compare
saved outputs; --write regenerates the JSON inventory and Markdown shortlist.
"""

import argparse
import json
from pathlib import Path

import numpy as np

import definable as board
from definability_audit import source_fingerprint

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--write", action="store_true")
args = parser.parse_args()
before = source_fingerprint()
snapshot = json.loads(Path("docs/definability_open/snapshot.json").read_text())
assert before == snapshot["fingerprint"], "Run the table audit first."
pos, neg = board.build_relations()
result = {"source_fingerprint": before, "variants": {}}
for flavour in ["all", "fin"]:
    p, n = pos["structural", flavour], neg["structural", flavour]
    reps, cls = board.preorder_quotient(p)
    reps = reps[1:]
    grid = np.ix_(reps, reps)
    rp, rn = p[grid], n[grid]
    gaps = []
    for i, j in np.argwhere(np.triu(~rn & ~rn.T & ~(rp & rp.T), 1)):
        a, b = int(reps[i]), int(reps[j])
        am, bm = (
            np.flatnonzero(cls == cls[a]).tolist(),
            np.flatnonzero(cls == cls[b]).tolist(),
        )
        gaps.append(
            dict(
                a=a,
                b=b,
                a_to_b="proved" if p[a, b] else "open",
                b_to_a="proved" if p[b, a] else "open",
                a_members=am,
                b_members=bm,
                weight=len(am) * len(bm),
            )
        )
    ga = np.array([x["a"] for x in gaps], dtype=int)
    gb = np.array([x["b"] for x in gaps], dtype=int)
    weights = np.array([x["weight"] for x in gaps], dtype=int)
    raw = int(weights.sum())
    assert raw == int(
        np.triu(~n[1:, 1:] & ~n[1:, 1:].T & ~(p[1:, 1:] & p[1:, 1:].T), 1).sum()
    )
    candidates = []
    for pair in gaps:
        for a, b in [(pair["a"], pair["b"]), (pair["b"], pair["a"])]:
            if p[a, b]:
                continue
            # A negative a -> b propagates to (u,v) when a -> u and v -> b.
            negative = (p[a, ga] & p[gb, b]) | (p[a, gb] & p[ga, b])
            # Adding one positive edge gives p' = p union p[:,a] x p[b,:].
            pab = p[ga, gb] | (p[ga, a] & p[b, gb])
            pba = p[gb, ga] | (p[gb, a] & p[b, ga])
            # The corresponding negative closure has these two extra rectangles.
            # A cross term would require n[a,b], impossible for this open edge.
            nab = n[ga, gb] | (p[b, ga] & n[a, gb]) | (n[ga, b] & p[gb, a])
            nba = n[gb, ga] | (p[b, gb] & n[a, ga]) | (n[gb, b] & p[ga, a])
            positive = (pab & pba) | nab | nba
            merged = reps[p[b, reps] & p[reps, a]].tolist() if p[b, a] else []
            candidates.append(
                dict(
                    source=a,
                    target=b,
                    reverse_proved=bool(p[b, a]),
                    positive_settles=int(positive.sum()),
                    negative_settles=int(negative.sum()),
                    positive_raw=int(weights[positive].sum()),
                    negative_raw=int(weights[negative].sum()),
                    positive_merges=max(0, len(merged) - 1),
                    merged_representatives=merged,
                )
            )
    # Balanced impact: either outcome should resolve several equivalence questions.
    candidates.sort(
        key=lambda x: (
            -min(x["positive_settles"], x["negative_settles"]),
            -x["positive_merges"],
            -x["negative_settles"],
            x["source"],
            x["target"],
        )
    )
    entry = dict(
        known_classes=len(reps),
        unresolved_class_pairs=len(gaps),
        both_open=sum(x["a_to_b"] == x["b_to_a"] == "open" for x in gaps),
        unresolved_raw_unordered_pairs=raw,
        pairs=gaps,
        candidates=candidates,
    )
    result["variants"][flavour] = entry
    print(
        flavour,
        {k: v for k, v in entry.items() if k not in ("pairs", "candidates")},
        flush=True,
    )
    # Independent full-quotient propagation for the displayed balanced leaders.
    for c in candidates[:12]:
        a, b = np.searchsorted(reps, c["source"]), np.searchsorted(reps, c["target"])
        pp = rp | np.outer(rp[:, a], rp[b, :])
        nn = pp.T @ rn @ pp.T
        old_gap = np.triu(~rn & ~rn.T & ~(rp & rp.T), 1)
        assert int((old_gap & (nn | nn.T | (pp & pp.T))).sum()) == c["positive_settles"]
        nn = rn | np.outer(rp[a, :], rp[:, b])
        assert int((old_gap & (nn | nn.T)).sum()) == c["negative_settles"]
assert source_fingerprint() == before, "Sources changed during computation."

lines = [
    "# FO-structural equivalence priorities",
    "",
    f"Date: {snapshot['date']}. All arrows are source → target.",
    "",
    "A gap is a pair of distinct proved equivalence classes with neither direction refuted. These are equivalence questions, not the much larger collection of individual open arrows.",
    "",
    "| Carriers | Proved classes | Unresolved class pairs | Both directions open | Raw unordered equation pairs |",
    "|---|---:|---:|---:|---:|",
]
for flavour, title in [("all", "Arbitrary"), ("fin", "Finite")]:
    e = result["variants"][flavour]
    lines.append(
        f"| {title} | {e['known_classes']} | {e['unresolved_class_pairs']} | {e['both_open']} | {e['unresolved_raw_unordered_pairs']} |"
    )
lines += [
    "",
    "The tables below rank open arrows by the smaller of their positive and negative impacts. Thus a leading target is useful whichever way it resolves. Counts refer to old unresolved class pairs in the indicated variant; they are conditional propagation counts, not predictions of which outcome holds. Counts for different targets overlap.",
    "",
]
for flavour, title in [("fin", "Finite carriers"), ("all", "Arbitrary carriers")]:
    e = result["variants"][flavour]
    lines += [
        f"## {title}: balanced targets",
        "",
        "| Source | Target | Pairs settled if positive | Pairs settled if negative | Classes merged if positive |",
        "|---:|---:|---:|---:|---|",
    ]
    for c in e["candidates"][:12]:
        merged = ", ".join(map(str, c["merged_representatives"])) or "none"
        lines.append(
            f"| {c['source']} | {c['target']} | {c['positive_settles']} | {c['negative_settles']} | {merged} |"
        )
    lines += [
        "",
        "## " + title + ": large conditional gains",
        "",
        "| Source | Target | Pairs settled if positive | Pairs settled if negative |",
        "|---:|---:|---:|---:|",
    ]
    top = sorted(
        e["candidates"],
        key=lambda x: (
            -max(x["positive_settles"], x["negative_settles"]),
            x["source"],
            x["target"],
        ),
    )[:6]
    lines += [
        f"| {c['source']} | {c['target']} | {c['positive_settles']} | {c['negative_settles']} |"
        for c in top
    ]
    lines.append("")
lines += [
    "## Validation",
    "",
    "The full positive and negative matrices were rebuilt from the audited sources. Weighted class-pair totals agree with an independent count over every raw unordered equation pair. The first twelve balanced candidates in each variant were independently checked by full Boolean matrix propagation on the quotient.",
    "",
    f"Source SHA-256: `{before['sha256']}`.",
    "",
    "[Complete pairs, memberships, and candidate impacts](../data/definability_structural_equivalence_gaps.json).",
    "",
    "Regenerate with `OPENBLAS_NUM_THREADS=2 python3 scripts/definability_structural_equivalence_gaps.py --write`.",
]
outputs = {
    Path("data/definability_structural_equivalence_gaps.json"): json.dumps(
        result, indent=2
    )
    + "\n",
    Path("docs/definability_structural_equivalence_gaps.md"): "\n".join(lines) + "\n",
}
for path, content in outputs.items():
    if args.write:
        path.write_text(content)
    else:
        assert path.read_text() == content, f"Stale FO inventory: {path}"
print("FO-structural inventory " + ("written." if args.write else "verified."))
