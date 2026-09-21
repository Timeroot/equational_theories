#!/usr/bin/env python3
"""Rebuild the finite and unrestricted term-structural equivalence inventory.

Run after definability_audit.py --write --verify-closure. The default checks the
saved JSON and report; --write regenerates both from the current relations.
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
    p, n = pos["termStructural", flavour], neg["termStructural", flavour]
    reps, cls = board.preorder_quotient(p)
    reps = reps[1:]
    grid = np.ix_(reps, reps)
    rp, rn = p[grid], n[grid]
    mask = np.triu(~rn & ~rn.T & ~(rp & rp.T), k=1)
    gaps = []
    for i, j in np.argwhere(mask):
        a, b = int(reps[i]), int(reps[j])
        ab, ba = ("proved" if p[a, b] else "open"), ("proved" if p[b, a] else "open")
        assert "open" in (ab, ba)
        gaps.append(
            dict(
                a=a,
                b=b,
                a_to_b=ab,
                b_to_a=ba,
                a_members=np.flatnonzero(cls == cls[a]).tolist(),
                b_members=np.flatnonzero(cls == cls[b]).tolist(),
            )
        )
    both = sum(x["a_to_b"] == x["b_to_a"] == "open" for x in gaps)
    raw = sum(len(x["a_members"]) * len(x["b_members"]) for x in gaps)
    assert raw == int(
        np.triu(~n[1:, 1:] & ~n[1:, 1:].T & ~(p[1:, 1:] & p[1:, 1:].T), 1).sum()
    )
    entry = dict(
        known_classes=len(reps),
        unresolved_class_pairs=len(gaps),
        both_open=both,
        one_proved_one_open=len(gaps) - both,
        unresolved_raw_unordered_pairs=raw,
        pairs=gaps,
    )
    result["variants"][flavour] = entry
    print(flavour, {k: v for k, v in entry.items() if k != "pairs"}, flush=True)
assert source_fingerprint() == before, "Sources changed during computation."

lines = [
    "# Remaining term-structural equivalence questions",
    "",
    f"Date: {snapshot['date']}. Computed from the same source fingerprint as the verified table audit.",
    "",
    "An unresolved pair is an unordered pair of distinct currently proved classes for which neither direction is refuted. Thus either both directions are open, or one is proved and the reverse is open. Open arrows whose reverse is refuted do not appear here.",
    "",
    "| Variant | Currently proved classes | Both directions open | One proved, reverse open | Total unresolved class pairs | Raw unordered equation pairs |",
    "|---|---:|---:|---:|---:|---:|",
]
for flavour, title in [("all", "Arbitrary carriers"), ("fin", "Finite carriers")]:
    e = result["variants"][flavour]
    lines.append(
        f"| {title} | {e['known_classes']} | {e['both_open']} | {e['one_proved_one_open']} | {e['unresolved_class_pairs']} | {e['unresolved_raw_unordered_pairs']} |"
    )
lines += [
    "",
    "Representatives are the least equation numbers in their currently proved classes. The two directions in the tables use the variant named in the heading. Class-pair counts are not counts of independent possible reductions in the number of classes.",
    "",
]
finite = result["variants"]["fin"]
if not finite["pairs"]:
    lines += [
        f"The finite equivalence classes are completely determined: there are exactly **{finite['known_classes']}**. Every two distinct classes have at least one refuted direction.",
        "",
    ]
pfin = pos["termStructural", "fin"]
if all(
    pfin[x["a"], x["b"]] and pfin[x["b"], x["a"]]
    for x in result["variants"]["all"]["pairs"]
):
    lines += [
        "All remaining unrestricted questions concern pairs already proved equivalent on finite carriers.",
        "",
    ]
# Record the specific separations which completed the finite classification.
for a, b in [(629, 52), (854, 433), (3342, 3545)]:
    assert neg["termStructural", "fin"][a, b]
lines += [
    "The [strict-implication counting proof](definability_spectrum_priority_pass.md) refutes E629 → E52 and E854 → E433. The [27-element product obstruction](definability_cube_focus.md) refutes E3342 → E3545. All three separations hold for both variants. E3545 → E3342 remains open.",
    "",
]
lines += [
    "The [unary-permutation obstruction](definability_equivalence_priority_pass.md) additionally refutes E1133 → E1096 and E1167 → E1096 on arbitrary carriers. Their finite equivalences remain proved.",
    "",
]
assert not pos["termStructural", "fin"][3545, 3342]
assert not neg["termStructural", "fin"][3545, 3342]
for flavour, title in [("fin", "Finite carriers"), ("all", "Arbitrary carriers")]:
    pairs = result["variants"][flavour]["pairs"]
    lines += [f"## {title}: complete list", ""]
    if not pairs:
        lines += ["No unresolved equivalence pairs.", ""]
        continue
    lines += ["| A | B | A → B | B → A |", "|---:|---:|---|---|"]
    members = {}
    for x in pairs:
        lines.append(f"| {x['a']} | {x['b']} | {x['a_to_b']} | {x['b_to_a']} |")
        members[x["a"]], members[x["b"]] = x["a_members"], x["b_members"]
    lines += [
        "",
        "### Participating class memberships",
        "",
        "| Representative | Equations in the class |",
        "|---:|---|",
    ]
    lines += [f"| {r} | {', '.join(map(str, members[r]))} |" for r in sorted(members)]
    lines.append("")
lines += [
    "## Validation",
    "",
    "The positive and negative matrices were rebuilt from the current sources. The source fingerprint matches the audited snapshot and did not change during the computation. Weighted class-pair counts were independently checked against the predicate on every raw unordered equation pair.",
    "",
    f"Source SHA-256: `{before['sha256']}`.",
    "",
    "Regenerate after the table audit with `OPENBLAS_NUM_THREADS=2 python3 scripts/definability_term_structural_equivalence_gaps.py --write`.",
    "",
    "[Machine-readable pairs and class memberships](../data/definability_term_structural_equivalence_gaps.json).",
]
outputs = {
    Path("data/definability_term_structural_equivalence_gaps.json"): json.dumps(
        result, indent=2
    )
    + "\n",
    Path("docs/definability_term_structural_equivalence_gaps.md"): "\n".join(lines)
    + "\n",
}
for path, content in outputs.items():
    if args.write:
        path.write_text(content)
    else:
        assert path.read_text() == content, f"Stale equivalence inventory: {path}"
print("Equivalence inventory " + ("written." if args.write else "verified."))
