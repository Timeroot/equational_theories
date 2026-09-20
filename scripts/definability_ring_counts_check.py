#!/usr/bin/env python3
"""Recount matrix and truncated-polynomial certificates using direct law evaluation."""
import argparse
from functools import lru_cache
import itertools
import json
from pathlib import Path
import numpy as np
from spectrum_generate import load_equations, variables

ROOT = Path(__file__).resolve().parents[1]


def term(t):
    if isinstance(t, str):
        return f'(.Leaf {"xyzuvw".index(t)})'
    return f"(.Fork {term(t[0])} {term(t[1])})"


def render(data, truncated):
    equations = load_equations()
    selected = [data["candidates"][i] for i in data["selected_indices"]]
    dimension_key = "degree" if truncated else "dimension"
    results = {}
    for index, (mod, dim, family) in enumerate(
        sorted({(e["modulus"], e[dimension_key], e["family"]) for e in selected})
    ):
        batch = [
            e
            for e in selected
            if (e["modulus"], e[dimension_key], e["family"]) == (mod, dim, family)
        ]
        counts = {e[k]: e[k + "_count"] for e in batch for k in ["source", "target"]}
        ring = (
            f"(Magma.TruncatedPolynomial.T (ZMod {mod}) {dim})"
            if truncated
            else f"(ZMod {mod})"
        )
        d = 1 if truncated else dim
        text = (
            (
                "import equational_theories.Definability.TruncatedPolynomialRing\n"
                if truncated
                else ""
            )
            + """import equational_theories.Definability.MatrixFamilyCounting

/-! Generated matrix-family counting certificates. -/
open Law Law.MagmaLaw Magma.MatrixFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

"""
        )
        split_counts = not truncated and (mod, dim, family) == (4, 2, "affine")
        if split_counts:
            text = (
                "".join(
                    f"import equational_theories.Definability.Generated.DeepMatrixZ4Count{law}\n"
                    for law in sorted(counts)
                )
                + text
            )
            text += "open Magma.DeepMatrixZ4\n\n"
        parameter = f'{"LP" if family=="linear" else "P"} {ring} {d}'
        param = "(p.1, p.2, 0)" if family == "linear" else "p"
        op = "lin" if family == "linear" else "op"
        oparg = f'{op} (R := {ring if truncated else f"ZMod {mod}"}) (d := {d})'
        prefix = "lin_" if family == "linear" else "op_"
        comp = "linComp" if family == "linear" else "comp"
        unit = "(1, 0) (0, 1)" if family == "linear" else "(1, 0, 0) (0, 1, 0)"
        for law in sorted(counts):
            l, r = equations[law - 1]
            k = 1 + max("xyzuvw".index(v) for v in variables(l) | variables(r))
            declaration = f"""def law{law} : MagmaLaw (Fin {k}) := ⟨{term(l)}, {term(r)}⟩
theorem count{law} : Fintype.card {{p : {parameter} // Test law{law} {param}}} = {counts[law]} := by
  native_decide

"""
            if split_counts:
                results[f"DeepMatrixZ4Count{law}.lean"] = (
                    "import equational_theories.Definability.MatrixFamilyCounting\n\n"
                    "/-! A single large matrix count, compiled separately for parallel checking. -/\n"
                    "open Law Law.MagmaLaw Magma.MatrixFamily\n"
                    "set_option maxRecDepth 100000\nset_option maxHeartbeats 2000000\n"
                    "namespace Magma.DeepMatrixZ4\n\n"
                    + declaration
                    + "end Magma.DeepMatrixZ4\n"
                )
            else:
                text += declaration.replace("def law", "private def law").replace(
                    "theorem count", "private theorem count"
                )
        for e in batch:
            s, t = e["source"], e["target"]
            k = 1 + max(
                "xyzuvw".index(v)
                for term0 in equations[t - 1]
                for v in variables(term0)
            )
            name = f'Equation{t}_not_termStructuralFromFin_Equation{s}_{"truncatedCount" if truncated else "deepMatrixCount"}'
            text += f"""theorem {name} : ¬ Law{t}.TermStructuralFromFin Law{s} := by
  apply not_termStructuralFromFin_of_cloneFamily_count ({oparg}) {prefix}injective
    {unit} {comp} {prefix}fst {prefix}snd {prefix}comp
    (fun p : {parameter} => Test law{s} {param})
    (fun p : {parameter} => Test law{t} {param})
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat {k} i))
  · rw [count{s}, count{t}]
    decide

"""
            if name in data.get("axioms", {}):
                text += (
                    "/-- info: "
                    + data["axioms"][name]
                    + " -/\n#guard_msgs (whitespace := lax) in\n"
                )
            text += f"#print axioms {name}\n\n"
        results[
            f'{"TruncatedCount" if truncated else "DeepMatrixCount"}{index}.lean'
        ] = text
    return results


def recount(equation, p, d, family, truncated):
    lhs, rhs = equation
    vs = sorted(variables(lhs) | variables(rhs))
    if truncated:
        order = p**d
        codes = np.arange(order)
        digits = np.array([codes // p**i % p for i in range(d)]).T
        add = np.zeros((order, order), dtype=np.int64)
        mul = np.zeros_like(add)
        for i in range(d):
            add += (digits[:, i, None] + digits[None, :, i]) % p * p**i
            mul += (
                sum(digits[:, j, None] * digits[None, :, i - j] for j in range(i + 1))
                % p
                * p**i
            )
        total = order ** (3 if family == "affine" else 2)
        answer = 0
        for start in range(0, total, 16384):
            code = np.arange(start, min(start + 16384, total))
            a = code % order
            b = code // order % order
            c = (
                code // order**2
                if family == "affine"
                else np.zeros(len(code), dtype=np.int64)
            )
            good = np.ones(len(code), dtype=bool)
            for marked in [None] + vs:

                def ev(t):
                    if isinstance(t, str):
                        return int(t == marked)
                    return add[add[mul[a, ev(t[0])], mul[b, ev(t[1])]], c]

                good &= ev(lhs) == ev(rhs)
            answer += int(good.sum())
        return answer
    order = p ** (d * d)
    size = p**d
    codes = np.arange(order)
    matrices = np.stack([codes // p**i % p for i in range(d * d)], axis=-1).reshape(
        order, d, d
    )
    codes = np.arange(size)
    vectors = np.stack([codes // p**i % p for i in range(d)], axis=-1)
    total = order**2 * (size if family == "affine" else 1)
    answer = 0
    for start in range(0, total, 4096):
        code = np.arange(start, min(start + 4096, total))
        a = matrices[code % order]
        b = matrices[code // order % order]
        c = (
            vectors[code // order**2]
            if family == "affine"
            else np.zeros((len(code), d), dtype=np.int64)
        )
        good = np.ones(len(code), dtype=bool)
        for marked, j in [(None, 0)] + list(itertools.product(vs, range(d))):

            def ev(t):
                if isinstance(t, str):
                    return np.broadcast_to(
                        (
                            np.eye(d, dtype=np.int64)[j]
                            if t == marked
                            else np.zeros(d, dtype=np.int64)
                        ),
                        c.shape,
                    )
                return (
                    np.einsum("nij,nj->ni", a, ev(t[0]))
                    + np.einsum("nij,nj->ni", b, ev(t[1]))
                    + c
                ) % p

            good &= np.all(ev(lhs) == ev(rhs), axis=-1)
        answer += int(good.sum())
    return answer


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--only", choices=["matrix", "truncated"])
    args = parser.parse_args()
    equations = load_equations()

    @lru_cache(None)
    def count(law, p, d, family, truncated):
        return recount(equations[law - 1], p, d, family, truncated)

    for label, truncated in [("matrix", False), ("truncated", True)]:
        if args.only and args.only != label:
            continue
        path = (
            ROOT
            / "data"
            / (
                "definability_truncated_counts.json"
                if truncated
                else "definability_deep_matrix_counts.json"
            )
        )
        data = json.loads(path.read_text())
        for e in data["candidates"]:
            for key in ["source", "target"]:
                actual = count(
                    e[key],
                    e["modulus"],
                    e["degree" if truncated else "dimension"],
                    e["family"],
                    truncated,
                )
                assert actual == e[key + "_count"], (e, key, actual)
        for filename, text in render(data, truncated).items():
            output = ROOT / "equational_theories/Definability/Generated" / filename
            if args.write:
                output.write_text(text)
            else:
                assert output.read_text() == text, f"Regenerate {output} with --write"
        print(
            f"{label}: independently verified {len(data['candidates'])} count obstructions.",
            flush=True,
        )


if __name__ == "__main__":
    main()
