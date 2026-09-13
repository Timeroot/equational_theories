"""Replay implication/duality paths as Lean spectrum inclusions.

The graph only selects proofs: generated Lean checks every edge and composition.
The input is the repository's full_entries.json, not an unverified closure table.
"""

import json
from collections import deque


def transfers(root, records, emit):
    duals = {i: i for i in range(1, 4695)}
    for a, b in json.loads((root / "data/duals.json").read_text()):
        duals[a], duals[b] = b, a
    edges = {}

    def add(a, b, proof):
        if a != b and (a, b) not in edges:
            edges[a, b] = proof

    # Prefer duality over a more expensive implication proof.
    for a, b in duals.items():
        add(a, b, {"kind": "duality"})
    for entry in json.loads((root / "full_entries.json").read_text()):
        implication = entry["variant"].get("implication")
        if not implication or not entry["proven"]:
            continue
        try:
            a, b = (int(implication[k].removeprefix("Equation")) for k in ["lhs", "rhs"])
        except ValueError:
            continue
        if not (1 <= a <= 4694 and 1 <= b <= 4694):
            continue
        proof = {"kind": "implication", "name": entry["name"],
                 "module": "equational_theories." + entry["filename"].split("equational_theories/")[-1]
                    .removesuffix(".lean").replace("/", "."),
                 "source": a, "target": b}
        add(a, b, proof)
        add(duals[a], duals[b], dict(proof, kind="dual_implication"))
    forward, reverse = {}, {}
    for a, b in edges:
        forward.setdefault(a, []).append(b)
        reverse.setdefault(b, []).append(a)

    def bfs(start, graph):
        parents = {start: None}
        queue = deque([start])
        while queue:
            a = queue.popleft()
            for b in sorted(graph.get(a, [])):
                if b not in parents:
                    parents[b] = a
                    queue.append(b)
        return parents

    from spectrum_generate import REPRESENTATIVES
    representatives, paths = {}, {}
    for rep in REPRESENTATIVES:
        out, into = bfs(rep, forward), bfs(rep, reverse)
        for i in out.keys() & into.keys():
            assert i not in representatives
            representatives[i] = rep
            path_in, a = [], i
            while a != rep:
                b = into[a]
                path_in.append((a, b))
                a = b
            path_out, a = [], i
            while a != rep:
                b = out[a]
                path_out.append((b, a))
                a = b
            paths[i] = (path_in, list(reversed(path_out)))
    nonfull = {r["equation"] for r in records if not r["full_spectrum"]}
    assert representatives.keys() == nonfull, nonfull - representatives.keys()
    assert sum(rep == 2 for rep in representatives.values()) == 1496
    used = set()
    special_paths = {}
    for a, b in [(125, 73), (880, 115), (1496, 481), (887, 695), (895, 898), (115, 873)]:
        parents = bfs(b, reverse)
        assert a in parents, (a, b)
        path, x = [], a
        while x != b:
            y = parents[x]
            path.append((x, y))
            x = y
        special_paths[a, b] = path
        used.update(path)
    for i, (into, out) in paths.items():
        used.update(into)
        if representatives[i] != 2:
            used.update(out)
    # Dual implications replay the original edge, conjugated by duality.
    extra = {(edges[e]["source"], edges[e]["target"]) for e in used
             if edges[e]["kind"] == "dual_implication"}
    used.update(extra)
    imports = sorted({edges[e]["module"] for e in used if "module" in edges[e]})
    lines = ["import equational_theories.Spectrum.Full", *[f"import {m}" for m in imports], "",
             "/-! Generated implication and duality transfers. No new proof assumptions. -/", "",
             "open Law Law.MagmaLaw", "namespace Spectrum.ImplicationTransfer", ""]

    def edge_name(a, b):
        return f"sub_{a}_{b}"

    # Original implications must precede their dual conjugates.
    for a, b in sorted(used, key=lambda e: (edges[e]["kind"] == "dual_implication", e)):
        proof = edges[a, b]
        lines += [f"theorem {edge_name(a,b)} : Law{a}.Subspectral Law{b} := by"]
        if proof["kind"] == "duality":
            lines += [f"  exact (spectrum_eq_of_isDual dual_{a}).subset"]
        elif proof["kind"] == "dual_implication":
            c, d = proof["source"], proof["target"]
            lines += [f"  unfold Subspectral", f"  rw [spectrum_eq_of_isDual dual_{a}, spectrum_eq_of_isDual dual_{b}]",
                      f"  exact {edge_name(c,d)}"]
        else:
            lines += ["  apply subspectral_iff_hasModel.mpr", "  rintro n ⟨M, hM⟩", "  letI := M",
                      f"  refine ⟨M, (@Law{b}.models_iff (Fin n) M).mpr ?_⟩",
                      f"  have h := (@Law{a}.models_iff (Fin n) M).mp hM",
                      f"  exact {proof['name']} (Fin n) h"]
        lines.append("")

    def compose(path):
        if not path:
            return "Subspectral.refl _"
        result = edge_name(*path[0])
        for e in path[1:]:
            result = f"({result}).trans {edge_name(*e)}"
        return result

    for (a, b), path in special_paths.items():
        lines += [f"theorem path_{a}_{b} : Law{a}.Subspectral Law{b} :=", f"  {compose(path)}", ""]

    for i in sorted(nonfull):
        rep = representatives[i]
        into, out = paths[i]
        if rep == 2:
            lines += [f"theorem singleton_{i} : Law{i}.spectrum = {{1}} := by",
                      "  apply Set.Subset.antisymm",
                      f"  · exact Set.Subset.trans ({compose(into)}) spectrum_two.subset",
                      "  · intro n hn", "    simpa only [Set.mem_singleton_iff.mp hn] using one_mem_spectrum _", ""]
        else:
            lines += [f"theorem spectrum_{i}_eq_{rep} : Law{i}.spectrum = Law{rep}.spectrum :=",
                      f"  Set.Subset.antisymm ({compose(into)}) ({compose(out)})", ""]
        record = records[i - 1]
        record["pdf_representative"] = rep
        if rep == 2:
            record.update(exact_spectrum="SINGLETON", exact_spectrum_theorem=f"Spectrum.ImplicationTransfer.singleton_{i}")
        else:
            record["representative_equality_theorem"] = f"Spectrum.ImplicationTransfer.spectrum_{i}_eq_{rep}"
    lines += ["end Spectrum.ImplicationTransfer", ""]
    emit(root / "equational_theories/Spectrum/Generated/ImplicationTransfer.lean", "\n".join(lines))
    return representatives
