#!/usr/bin/env python3
"""Generate spectrum certificates and the complete note catalogue for E1–E4694.

Python selects witnesses and complete refutation trees; Lean checks the resulting
certificates. The catalogue additionally specifies the note's stated results
with explicitly indexed proof obligations. No exclusion is justified by a Python
search failure, and no question-marked exact spectrum is asserted as a theorem.
"""

import argparse
from collections import Counter
from itertools import product
from pathlib import Path
import json
import re
from spectrum_bv import PROVED_CASES, certificate_files

ROOT = Path(__file__).resolve().parent.parent
REPRESENTATIVES = [2, 63, 66, 73, 115, 118, 125, 167, 168, 467, 474, 481, 501, 546, 556,
                   667, 670, 677, 695, 704, 873, 880, 883, 887, 895, 898, 907, 1076, 1083,
                   1110, 1279, 1286, 1313, 1323, 1480, 1483, 1485, 1486, 1489, 1496, 1516,
                   1526, 1685, 1692, 1719]


def parse_term(text):
    tokens = re.findall(r"[a-z]+|[()◇]", text)
    pos = 0

    def atom():
        nonlocal pos
        token = tokens[pos]
        pos += 1
        if token != "(":
            assert token not in (")", "◇")
            return token
        term = expr()
        assert tokens[pos] == ")"
        pos += 1
        return term

    def expr():
        nonlocal pos
        term = atom()
        while pos < len(tokens) and tokens[pos] == "◇":
            pos += 1
            term = (term, atom())
        return term

    term = expr()
    assert pos == len(tokens)
    return term


def coefficients(term, a, b):
    if isinstance(term, str):
        return {term: 1}
    left = coefficients(term[0], a, b)
    right = coefficients(term[1], a, b)
    return {v: a * left.get(v, 0) + b * right.get(v, 0)
            for v in left.keys() | right.keys()}


def equal_coefficients(lhs, rhs, a, b, modulus=0):
    left = coefficients(lhs, a, b)
    right = coefficients(rhs, a, b)
    differences = [left.get(v, 0) - right.get(v, 0)
                   for v in left.keys() | right.keys()]
    return all(d % modulus == 0 if modulus else d == 0 for d in differences)


def variables(term):
    if isinstance(term, str):
        return {term}
    return variables(term[0]) | variables(term[1])


def evaluate(term, assignment, table, n):
    if isinstance(term, str):
        return assignment[term]
    return table[n * evaluate(term[0], assignment, table, n)
                 + evaluate(term[1], assignment, table, n)]


def satisfies(lhs, rhs, table, n):
    vs = sorted(variables(lhs) | variables(rhs))
    for vals in product(range(n), repeat=len(vs)):
        assignment = dict(zip(vs, vals))
        if evaluate(lhs, assignment, table, n) != evaluate(rhs, assignment, table, n):
            return False
    return True


def load_equations():
    lines = (ROOT / "data/equations.txt").read_text().splitlines()
    assert len(lines) == 4694
    return [tuple(map(parse_term, line.split("="))) for line in lines]


def classify(equations):
    linear = {}
    two = {}
    for i, (lhs, rhs) in enumerate(equations, 1):
        for a, b in [(0, 0), (1, 0), (0, 1), (-1, -1), (1, -1), (-1, 1), (1, 1)]:
            if equal_coefficients(lhs, rhs, a, b):
                linear[i] = (a, b)
                break
        if i not in linear:
            two[i] = next((table for table in product(range(2), repeat=4)
                           if satisfies(lhs, rhs, table, 2)), None)
    return linear, two


def search_finite(lhs, rhs, n=3):
    """A decision tree with an explicit falsifying assignment at every closed leaf."""
    vs = sorted(variables(lhs) | variables(rhs))
    assignments = [(vals, dict(zip(vs, vals))) for vals in product(range(n), repeat=len(vs))]
    table = [None] * (n * n)

    def partial(term, assignment, needed):
        if isinstance(term, str):
            return assignment[term]
        x = partial(term[0], assignment, needed)
        y = partial(term[1], assignment, needed)
        if x is None or y is None:
            return None
        cell = n * x + y
        if table[cell] is None:
            needed[cell] += 1
        return table[cell]

    def search():
        needed = Counter()
        for vals, assignment in assignments:
            x = partial(lhs, assignment, needed)
            y = partial(rhs, assignment, needed)
            if x is not None and y is not None and x != y:
                return {"values": vals, "left": x, "right": y}
        if not needed:
            return {"model": [0 if v is None else v for v in table]}
        cell = needed.most_common(1)[0][0]
        branches = []
        for value in range(n):
            table[cell] = value
            child = search()
            if "model" in child:
                table[cell] = None
                return child
            branches.append(child)
        table[cell] = None
        return {"split": cell, "branches": branches}

    return search()


def print_tree(tree, indent="  ", hypotheses=(), n=3):
    if "values" in tree:
        args = " ".join(map(str, tree["values"]))
        return [f"{indent}exact (by decide : ({tree['left']} : Fin {n}) ≠ {tree['right']})",
                f"{indent}  (by simpa only [{', '.join(hypotheses)}] using h {args})"]
    cell = tree["split"]
    name = f"h{cell}"
    lines = [f"{indent}rcases split {cell // n} {cell % n} with {' | '.join([name] * n)}"]
    for branch in tree["branches"]:
        child = print_tree(branch, indent + "  ", hypotheses + (name,), n)
        child[0] = indent + "· " + child[0].lstrip()
        lines.extend(child)
    return lines


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true", help="regenerate the Lean certificate files")
    mode.add_argument("--check", action="store_true", help="check that generated files are current, without writing")
    args = parser.parse_args()
    equations = load_equations()
    linear, two = classify(equations)
    print("Integer linear full spectra:", len(linear), dict(Counter(linear.values())))
    print("Other laws without a two-element model:", sum(t is None for t in two.values()))
    print("Other laws with a two-element model:", [i for i, t in two.items() if t is not None])
    three = {i: search_finite(*equations[i - 1]) for i, t in two.items() if t is not None}
    print("Of these, laws with a three-element model:", [i for i, t in three.items() if "model" in t])
    independent = {i for i, (lhs, rhs) in enumerate(equations, 1)
                   if isinstance(lhs, str) and lhs not in variables(rhs)}
    singleton_source = (ROOT / "equational_theories/Generated/Singleton.lean").read_text()
    singleton_lemmas = {int(i) for i in re.findall(r"theorem Equation(\d+)_implies_Equation2\b", singleton_source)}
    direct_singletons = independent | singleton_lemmas | {2}
    duals = {i: i for i in range(1, 4695)}
    for i, j in json.loads((ROOT / "data/duals.json").read_text()):
        duals[i] = j
        duals[j] = i
    singletons = direct_singletons | {duals[i] for i in direct_singletons}
    print("Direct/dual singleton certificates (before implication transfer):", len(singletons))
    if not args.write and not args.check:
        return
    def emit(path, content):
        if args.check:
            if not path.exists() or path.read_text() != content:
                raise SystemExit(f"Stale generated file: {path.relative_to(ROOT)}")
        elif not path.exists() or path.read_text() != content:
            path.write_text(content)

    output = ROOT / "equational_theories/Spectrum/Generated"
    if args.write:
        output.mkdir(parents=True, exist_ok=True)
    for start in range(1, 4695, 500):
        entries = [(i, ab) for i, ab in linear.items() if start <= i < start + 500]
        lines = ["import equational_theories.Spectrum.Linear", "import equational_theories.Equations.All", "",
                 "/-! Generated by `scripts/spectrum_generate.py`. Every coefficient certificate",
                 "is checked in the Lean kernel by `decide`. -/", "", "namespace Spectrum", ""]
        for i, (a, b) in entries:
            lines += [f"theorem full_{i} : Law{i}.HasFullSpectrum :=",
                      f"  full_of_linear Law{i} ({a}) ({b}) (by decide)", ""]
        lines += ["end Spectrum", ""]
        emit(output / f"Linear{start:04d}.lean", "\n".join(lines))
    lines = ["import equational_theories.Spectrum.Finite", "import equational_theories.Equations.All", "",
             "/-! Generated by `scripts/spectrum_generate.py`. Witnesses at order two",
             "for the laws not already handled by integer linear models. -/", "", "namespace Spectrum", ""]
    for i, table in two.items():
        if table is not None:
            a, b, c, d = table
            magma = f"table2 {a} {b} {c} {d}"
            lines += [f"theorem two_{i} : Law{i}.HasModel 2 :=",
                      f"  ⟨{magma}, (@Law{i}.models_iff (Fin 2) ({magma})).mpr (by decide)⟩", ""]
    lines += ["end Spectrum", ""]
    emit(output / "Two.lean", "\n".join(lines))
    lines = ["import equational_theories.Spectrum.Full", "import equational_theories.Generated.Singleton", "",
             "/-! Generated by `scripts/spectrum_generate.py`. Singleton spectra, from a free",
             "variable on one side or an existing implication to Equation2. -/", "", "namespace Spectrum", ""]
    for i in sorted(direct_singletons - {2}):
        if i in independent:
            k = len(variables(equations[i - 1][0]) | variables(equations[i - 1][1]))
            rhs_args = " ".join(["y"] * k)
            lhs_args = " ".join(["x"] + ["y"] * (k - 1))
            lines += [f"theorem singleton_{i} : Law{i}.spectrum = {{1}} :=",
                      "  singleton_of_implies (fun {G} M h => by",
                      "    apply (@Law2.models_iff G M).mpr", f"    have h' := (@Law{i}.models_iff G M).mp h",
                      "    intro x y", f"    exact (h' {lhs_args}).trans (h' {rhs_args}).symm)", ""]
        else:
            lines += [f"theorem singleton_{i} : Law{i}.spectrum = {{1}} :=",
                      "  singleton_of_implies (fun {G} M h =>",
                      f"    (@Law2.models_iff G M).mpr (Singleton.Equation{i}_implies_Equation2 G",
                      f"      ((@Law{i}.models_iff G M).mp h)))", ""]
    for i in sorted(singletons - direct_singletons):
        lines += [f"theorem singleton_{i} : Law{i}.spectrum = {{1}} :=",
                  f"  (Law.MagmaLaw.spectrum_eq_of_isDual dual_{i}).trans singleton_{duals[i]}", ""]
    lines += ["end Spectrum", ""]
    emit(output / "Singleton.lean", "\n".join(lines))
    modular = {}
    lines = ["import equational_theories.Spectrum.Linear", "import equational_theories.Equations.All", "",
             "/-! Generated by `scripts/spectrum_generate.py`. Positive modular witnesses for",
             "the 45 non-full representatives in §3.1 of the note. Search failures assert nothing. -/", "",
             "set_option maxRecDepth 4096", "set_option maxHeartbeats 2000000", "",
             "open Law Law.MagmaLaw", "namespace Spectrum", ""]
    for i in REPRESENTATIVES:
        for n in [3, 4, 5, 7, 8, 9, 11, 13, 16]:
            ab = next(((a, b) for a, b in product(range(n), repeat=2)
                       if equal_coefficients(*equations[i - 1], a, b, n)), None)
            if ab is None:
                continue
            a, b = ab
            modular.setdefault(i, []).append(n)
            magma = f"linear (G := ZMod {n}) {a} {b}"
            lines += [f"theorem model_{i}_{n} : Law{i}.HasModel {n} :=",
                      f"  hasModel_of_card ({magma})",
                      f"    ((@Law{i}.models_iff (ZMod {n}) ({magma})).mpr (by decide))",
                      f"    (ZMod.card {n})", ""]
    lines += ["end Spectrum", ""]
    emit(output / "Modular.lean", "\n".join(lines))
    for path, content in certificate_files().items():
        emit(path, content)
    lines = [*[f"import equational_theories.Spectrum.Generated.BV{i}_{n}" for i, n in PROVED_CASES], "",
             "/-! Integrated symmetry-broken bit-vector exclusions. Each assembled proof",
             "is checked complete below; total compilation timings are in docs/spectrum_bv.md. -/", "",
             "namespace Spectrum", ""]
    for i, n in PROVED_CASES:
        lines += [f"theorem not_order_{i}_{n} : ¬ Law{i}.HasModel {n} :=",
                  f"  BitExclusion.not_order_{i}_{n}",
                  f"spectrum_assert not_order_{i}_{n} complete", ""]
    lines += ["end Spectrum", ""]
    emit(output / "SmallExclusions.lean", "\n".join(lines))
    full = set(linear) | {i for i, t in three.items() if "model" in t}
    assert full == set(linear) | {1482, 1523, 1682, 1885, 2125, 2132}
    records = []
    for i in range(1, 4695):
        missing = [] if i in full else [2 if two[i] is None else 3]
        exact = ("POSITIVE" if i in full else "SINGLETON" if i in singletons else
                 "POSITIVE_EXCEPT_2" if i in {1685, 1922} else "UNKNOWN")
        exact_theorem = (f"Spectrum.full_{i}" if i in full else
                         "Spectrum.spectrum_two" if i == 2 else
                         f"Spectrum.singleton_{i}" if i in singletons else
                         f"Spectrum.spectrum_{i}" if i in {1685, 1922} else None)
        records.append({"equation": i, "full_spectrum": i in full, "exact_spectrum": exact,
                        "exact_spectrum_theorem": exact_theorem,
                        "excluded_orders": missing,
                        "explicit_orders": sorted({1} | ({2} if i in two and two[i] is not None else set())
                                                  | set(modular.get(i, []))),
                        "full_or_exclusion_theorem": f"Spectrum.full_{i}" if i in full else
                            f"Spectrum.not_{'two' if missing == [2] else 'three'}_{i}"})
    from spectrum_transfer import transfers
    _, edges = transfers(ROOT, records, emit)
    from spectrum_negative import negative_basis
    seeds, routes = negative_basis(ROOT, records, edges, emit)
    lines = ["import equational_theories.Spectrum.Finite", "import equational_theories.Spectrum.Status",
             "import equational_theories.Spectrum.Generated.NegativeTransfer", "",
             "/-! Compact exhaustive checks only at the exclusion basis. All other results",
             "are transferred through proved implication/duality/definability constructions.",
             "The loops have 2^4=16 or 3^9=19683 operations, with no generated case tree. -/", "",
             "namespace Spectrum", ""]
    for i, n in sorted(seeds):
        if n not in [2, 3]:
            continue
        word = 'two' if n == 2 else 'three'
        lines += ["@[spectrum_native]", f"theorem native_seed_{i}_{n} : ¬ Law{i}.HasModel {n} :=",
                  f"  not_{word}_of_equation Law{i} (@Equation{i} (Fin {n}))",
                  f"    (@Law{i}.models_iff (Fin {n})) (by native_decide)",
                  f"spectrum_assert native_seed_{i}_{n} complete", ""]
    for (i, n), b in sorted(routes.items()):
        if n not in [2, 3]:
            continue
        name = (f"not_{'two' if n == 2 else 'three'}_{i}" if records[i - 1]['excluded_orders'] == [n]
                else f"not_order_{i}_{n}")
        lines += [f"theorem {name} : ¬ Law{i}.HasModel {n} :=",
                  f"  (NegativeTransfer.route_{i}_{n}).not_hasModel native_seed_{b}_{n}", ""]
    lines += ["end Spectrum", ""]
    emit(output / "SmallOrder.lean", "\n".join(lines))
    from spectrum_quasigroup_six import certificate as quasigroup_certificate
    emit(ROOT / "equational_theories/Spectrum/QuasigroupSix.lean", quasigroup_certificate())
    from spectrum_small_certificates import generate as small_certificates
    small_certificates(ROOT, emit)
    from spectrum_1489_seeds import certificate_files as idempotent_1489_certificates
    for path, content in idempotent_1489_certificates().items():
        emit(path, content)
    from spectrum_catalogue import catalogue
    catalogue(ROOT, records, emit, seeds, routes)
    emit(ROOT / "data/spectrum/catalogue.json", json.dumps(records, indent=2) + "\n")
    imports = [f"import equational_theories.Spectrum.Generated.{kind}{start:04d}"
               for kind in ["Linear"] for start in range(1, 4695, 500)]
    imports += [f"import equational_theories.Spectrum.Generated.{kind}" for kind in ["Two", "Singleton", "Modular", "SmallOrder", "SmallExclusions", "ImplicationTransfer"]]
    emit(ROOT / "equational_theories/Spectrum/Generated.lean", "\n".join(imports) + "\n")
    print("Exact spectra:", dict(Counter(r["exact_spectrum"] for r in records)))
    print("Modular witnesses:", sum(map(len, modular.values())))
    if args.check:
        print("Generated files are current.")


if __name__ == "__main__":
    main()
