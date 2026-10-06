#!/usr/bin/env python3
"""Bounded E667/12 search with left translations in PGL(2,11).

This is only a restricted construction family. A timeout has no negative
meaning, and a family refutation does not exclude arbitrary order12 models.
The formula omits canonical-row normalization because arbitrary relabeling
need not preserve this specified projective action.
"""
import sys, json, itertools, time, subprocess, argparse
from pathlib import Path

from spectrum_667_incremental import clauses
from spectrum_generate import load_equations, satisfies

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--seconds", type=int, default=90)
args = parser.parse_args()
assert args.seconds > 0
q = 11
n = 12
R = range(n)
perms = set()
for a, b, c, d in itertools.product(range(q), repeat=4):
    if (a * d - b * c) % q == 0:
        continue
    row = []
    for x in R:
        num, den = (a, c) if x == q else ((a * x + b) % q, (c * x + d) % q)
        row.append(q if den == 0 else num * pow(den, -1, q) % q)
    perms.add(tuple(row))
perms = sorted(perms)
assert len(perms) == 1320
assert all(sorted(row) == list(R) for row in perms)
cs = clauses(n, "unnormalized")
base = 2 * n**3
p = lambda x, y, z: 1 + (x * n + y) * n + z
for x in R:
    vs = [base + x * len(perms) + i + 1 for i in range(len(perms))]
    cs.append(vs)
    for v, row in zip(vs, perms):
        cs.extend([[-v, p(x, y, z)] for y, z in enumerate(row)])
path = Path(".cache/e667-hard/projective12.cnf")
path.parent.mkdir(parents=True, exist_ok=True)
path.write_text(
    f"p cnf {base+n*len(perms)} {len(cs)}\n"
    + "".join(" ".join(map(str, c)) + " 0\n" for c in cs)
)
t = time.monotonic()
cp = subprocess.run(
    ["cadical", "--quiet", "-t", str(args.seconds), str(path)],
    capture_output=True,
    text=True,
)
r = {
    "order": 12,
    "scope": "All left translations lie in PGL(2,11), acting on the projective line; restricted family only",
    "group_size": len(perms),
    "limit_seconds": args.seconds,
    "seconds": time.monotonic() - t,
    "status": {10: "SAT", 20: "UNSAT"}.get(cp.returncode, "UNKNOWN"),
}
if cp.returncode == 10:
    vs = {
        int(s)
        for l in cp.stdout.splitlines()
        if l.startswith("v ")
        for s in l.split()[1:]
    }
    table = [
        next(z for z in R if p(x, y, z) in vs)
        for x, y in itertools.product(R, repeat=2)
    ]
    assert satisfies(*load_equations()[666], table, n)
    r["table"] = table
Path(".cache/e667-hard/projective12.json").write_text(json.dumps(r, indent=2) + "\n")
path.unlink()
print(r)
