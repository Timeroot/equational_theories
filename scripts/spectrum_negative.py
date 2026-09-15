"""Choose a small exclusion basis using implication, duality AND definability.

Graph search chooses existing theorem applications, never proves an exclusion.
Every chosen edge is replayed by Lean. This is separate from the PDF's fixed
45-class naming convention, since definability can merge more classes.
"""
import re
from collections import defaultdict, deque
from spectrum_bv import PROVED_CASES


def negative_basis(root, records, edges, emit):
    from spectrum_note import EXCLUDED
    edges = dict(edges)
    pattern = re.compile(r"theorem\s+(\w+)\s*:\s*Law(\d+)\."
        r"(TermDefinableFromFin|TermDefinableFrom|TermStructuralFromFin|TermStructuralFrom|"
        r"StructuralFromFin|StructuralFrom|DefinableFromFin|DefinableFrom)\s+Law(\d+)")
    modules = ["PositiveTerms", "PositiveTermsFin", "PositiveStructural", "PositiveTermsBig",
               "Parastrophic", "DivisionCover", "Cover"]
    bridges = {"TermDefinableFromFin": "termDefinableFin", "TermDefinableFrom": "termDefinable",
               "TermStructuralFromFin": "termStructuralFin", "TermStructuralFrom": "termStructural",
               "StructuralFromFin": "structuralFin", "StructuralFrom": "structural",
               "DefinableFromFin": "definableFin", "DefinableFrom": "definable"}
    count = 0
    for module in modules:
        path = root / f"equational_theories/Definability/{module}.lean"
        for name, target, kind, source in pattern.findall(path.read_text()):
            a, b = int(source), int(target)
            if not (1 <= a <= 4694 and 1 <= b <= 4694):
                continue
            count += 1
            edges.setdefault((a, b), {"kind": "definability", "name": name,
                "bridge": bridges[kind], "module": f"equational_theories.Definability.{module}"})
    reverse = defaultdict(list)
    for a, b in edges:
        reverse[b].append(a)

    def paths_to(b):
        parents, queue = {b: None}, deque([b])
        while queue:
            y = queue.popleft()
            for x in sorted(reverse[y]):
                if x not in parents:
                    parents[x] = y
                    queue.append(x)
        return parents

    # Small established exclusions plus all PDF-reported individual exclusions.
    wanted = {(r['equation'], n) for r in records for n in r['excluded_orders']}
    wanted.update((i, n) for i, sizes in EXCLUDED.items() for n in sizes)
    wanted.update(PROVED_CASES)
    wanted.add((1480, 3))
    original_wanted = wanted
    wanted = {(records[i - 1].get('pdf_representative', i), n) for i, n in wanted}
    candidates = defaultdict(set)
    for i, n in wanted:
        candidates[n].add(i)
    chosen, selected_paths = set(), {}
    for n, options in sorted(candidates.items()):
        remaining = {i for i, size in wanted if size == n}
        reach = {b: paths_to(b) for b in options}
        while remaining:
            # Prefer completed BV proofs to missing finite certificates.
            b = min(options, key=lambda b: (0 if (b, n) in PROVED_CASES else 1,
                                            -len(remaining & reach[b].keys()), b))
            covered = remaining & reach[b].keys()
            if not covered:
                options.remove(b)
                continue
            chosen.add((b, n))
            for i in covered:
                path, x = [], i
                while x != b:
                    y = reach[b][x]
                    path.append((x, y))
                    x = y
                selected_paths[i, n] = path
            remaining -= covered
            options.remove(b)
    used = {e for path in selected_paths.values() for e in path}
    # Replay a conjugated original implication directly; no unproved graph facts.
    imports = sorted({edges[e]['module'] for e in used if 'module' in edges[e]})
    lines = ["import equational_theories.Spectrum.Definability", "import equational_theories.Duals.All",
             "import equational_theories.Spectrum.Generated.ImplicationTransfer",
             *[f"import {m}" for m in imports], "", "/-! Exclusion propagation selected from existing proved",
             "implication, duality, and definability theorems. No finite search here. -/", "",
             "open Law Law.MagmaLaw", "namespace Spectrum.NegativeTransfer", ""]
    def implication(p, indent):
        a, b = p['source'], p['target']
        return [indent + "apply subspectral_iff_hasModel.mpr", indent + "rintro n ⟨M, hM⟩",
                indent + "letI := M", indent + f"refine ⟨M, (@Law{b}.models_iff (Fin n) M).mpr ?_⟩",
                indent + f"exact {p['name']} (Fin n) ((@Law{a}.models_iff (Fin n) M).mp hM)"]
    for a, b in sorted(used):
        p = edges[a, b]
        lines += [f"theorem sub_{a}_{b} : Law{a}.Subspectral Law{b} := by"]
        if p['kind'] == 'duality':
            lines += [f"  exact (spectrum_eq_of_isDual dual_{a}).subset"]
        elif p['kind'] == 'definability':
            lines += [f"  exact subspectral_of_{p['bridge']} {p['name']}"]
        elif p['kind'] == 'implication':
            lines += implication(p, "  ")
        else:
            lines += [f"  unfold Subspectral", f"  rw [spectrum_eq_of_isDual dual_{a}, spectrum_eq_of_isDual dual_{b}]",
                      f"  change Law{p['source']}.Subspectral Law{p['target']}"]
            lines += implication(p, "  ")
        lines.append("")
    for (rep, n), path in sorted(selected_paths.items()):
        b = path[-1][1] if path else rep
        proof = "Subspectral.refl _" if not path else f"sub_{path[0][0]}_{path[0][1]}"
        for a, c in path[1:]:
            proof = f"({proof}).trans sub_{a}_{c}"
        lines += [f"theorem basis_route_{rep}_{n} : Law{rep}.Subspectral Law{b} := {proof}", ""]
    destinations = {}
    for i, n in sorted(original_wanted):
        rep = records[i - 1].get('pdf_representative', i)
        path = selected_paths[rep, n]
        b = path[-1][1] if path else rep
        destinations[i, n] = b
        proof = f"basis_route_{rep}_{n}"
        if i != rep:
            eq = (f"ImplicationTransfer.singleton_{i} |>.trans spectrum_two.symm" if rep == 2 else
                  f"ImplicationTransfer.spectrum_{i}_eq_{rep}")
            proof = f"(show Law{i}.Subspectral Law{rep} from ({eq}).subset).trans {proof}"
        lines += [f"theorem route_{i}_{n} : Law{i}.Subspectral Law{b} := {proof}", ""]
    lines += ["end Spectrum.NegativeTransfer", ""]
    emit(root / "equational_theories/Spectrum/Generated/NegativeTransfer.lean", "\n".join(lines))
    print(f"Negative basis: checked {count} definability results; {len(original_wanted)} exclusions use {len(chosen)} seeds:", sorted(chosen))
    print("Selected definability edges:", [(a, b) for a, b in used if edges[a,b]['kind'] == 'definability'])
    return chosen, destinations
