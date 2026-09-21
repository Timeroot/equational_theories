#!/usr/bin/env python3
"""Emit or retry the saved, bounded search for unrestricted recovery witnesses.

Without --vampire, only TPTP problems are written. A failed or timed-out proof
search is never reported as a mathematical refutation. No board files are changed.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def parse_term(text):
    tokens = re.findall(r"[xyzwuv()]|◇", text)
    pos = 0

    def atom():
        nonlocal pos
        token = tokens[pos]
        pos += 1
        if token != "(":
            assert token in "xyzwuv"
            return token
        left = expression()
        assert tokens[pos] == ")"
        pos += 1
        return left

    def expression():
        nonlocal pos
        term = atom()
        while pos < len(tokens) and tokens[pos] == "◇":
            pos += 1
            term = (term, atom())
        return term

    result = expression()
    assert pos == len(tokens), text
    return result


def variables(term, env):
    if isinstance(term, str):
        return env[term]
    return tuple(variables(child, env) for child in term)


def operation(term, witness):
    if isinstance(term, str):
        return term
    return variables(witness, dict(zip("xy", (operation(t, witness) for t in term))))


def tptp(term):
    if isinstance(term, str):
        return term.upper()
    return f"m({tptp(term[0])},{tptp(term[1])})"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--vampire", type=Path)
    parser.add_argument("--seconds", type=int, default=3)
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    saved = json.loads((ROOT / "data/definability_equivalence_recovery_probe.json").read_text())
    laws = [tuple(parse_term(side) for side in line.split("="))
            for line in (ROOT / "data/equations.txt").read_text().splitlines() if line.strip()]
    jobs = []
    for i, candidate in enumerate(saved["candidates"]):
        source, target = candidate["source"], candidate["target"]
        witness, inverse = map(parse_term, (candidate["w"], candidate["v"]))
        obligations = {
            "law": tuple(operation(t, witness) for t in laws[target - 1]),
            "back": (operation(inverse, witness), ("x", "y")),
        }
        for kind, goal in obligations.items():
            path = args.output / f"{source}_{target}_{i}_{kind}.p"
            lines = []
            for name, role, equation in (("source", "axiom", laws[source - 1]),
                                         ("goal", "conjecture", goal)):
                left, right = map(tptp, equation)
                lines.append(f"fof({name},{role},![X,Y,Z,W,U,V]: {left}={right}).")
            path.write_text("\n".join(lines) + "\n")
            jobs.append((path, source, target, kind, i))
    print(f"Emitted {len(jobs)} obligations for {len(saved['candidates'])} candidates.", flush=True)
    if args.vampire is None:
        return

    def run(job):
        path, source, target, kind, index = job
        result = subprocess.run(
            [str(args.vampire.resolve()), "--mode", "casc", "-t", str(args.seconds), str(path)],
            capture_output=True, text=True, check=False)
        path.with_suffix(".log").write_text(result.stdout + result.stderr)
        status = re.findall(r"SZS status (\w+)", result.stdout)
        return dict(source=source, target=target, kind=kind, candidate=index,
                    status=status[-1] if status else "no_status", exit_code=result.returncode)

    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        results = list(pool.map(run, jobs))
    (args.output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(f"Proved {sum(r['status'] == 'Theorem' for r in results)} obligations.")


if __name__ == "__main__":
    main()
