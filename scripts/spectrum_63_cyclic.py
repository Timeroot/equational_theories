#!/usr/bin/env python3
"""Generate small cyclic-template searches for E63 via E229.

The automorphism consists of one q-cycle and p fixed points. All fixed-point
translations on that cycle are cyclic shifts. The mathematical reductions and
completeness of the shift-set enumeration are in docs/63_orders26_30.md.

This searches a restricted construction class, never all magmas of order q+p.
Only directly checked tables are accepted as models; solver negatives are not
Lean proofs. Requires python-sat and (unless --generate-only) CaDiCaL.
"""
import argparse, sys, time, json, subprocess, gzip, itertools, math
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from pysat.card import CardEnc, EncType

sys.path.insert(0, str(Path(__file__).resolve().parent))
from spectrum_63_bennett import prime, gf_affine
from spectrum_63_atp import validate

if not __debug__:
    raise RuntimeError("Do not disable assertions when checking model certificates")

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("cycle_length", type=int)
parser.add_argument("fixed_points", type=int)
parser.add_argument("--output", type=Path, required=True)
parser.add_argument("--seconds", type=int, default=5)
parser.add_argument("--jobs", type=int, default=4)
parser.add_argument("--generate-only", action="store_true")
args = parser.parse_args()
q, p = args.cycle_length, args.fixed_points
n = q + p
root = args.output
root.mkdir(parents=True, exist_ok=True)
if q < 3 or q % 4 == 0 or p not in [1, 3, 4, 5, 7]:
    parser.error(
        "This audited generator supports q >= 3, q not divisible by 4, and p in {1,3,4,5,7}."
    )
if args.seconds < 1 or args.jobs < 1:
    parser.error("Resource limits must be positive.")
P = gf_affine(4, 7, 2, 2) if p == 4 else prime(p, False) if p > 1 else [[0]]
units = [u for u in range(1, q) if math.gcd(u, q) == 1]


def allowed(A):
    if q % 2 and 0 in A:
        return False
    if q % 2 == 0 and q // 2 in A:
        return False
    B = {2 * a % q for a in A}
    if len(B) != p or (B & {-b % q for b in B}) - {0}:
        return False
    U = set(A) | B | {-b % q for b in B}
    return len(U | ({0} if q % 3 else set())) + p <= q


cases = sorted(
    {
        min(tuple(sorted(a * u % q for a in A)) for u in units)
        for A in itertools.combinations(range(q), p)
        if allowed(A)
    }
)
print(q, p, "canonical shift sets", len(cases), flush=True)
(root / f"one-orbit-{q}-{p}-cases.json").write_text(json.dumps(cases, indent=2) + "\n")


def run(it):
    index, A = it
    name = f"one-orbit-{q}-{p}-{index}"
    clauses = []
    top = q * n

    def lit(x, y, z):
        if x >= q:
            out = q + P[x - q][y - q] if y >= q else (y + A[x - q]) % q
            return out == z
        if y >= q:
            return (x - 2 * A[y - q]) % q == z
        return 1 + (y - x) % q * n + ((z - x) % q if z < q else z)

    def neg(v):
        return not v if type(v) is bool else -v

    def clause(vs):
        if any(v is True for v in vs):
            return
        clauses.append([v for v in vs if v is not False])

    def exactly(vs):
        nonlocal top
        fixed = sum(v is True for v in vs)
        vs = [v for v in vs if type(v) is int]
        if fixed > 1:
            clauses.append([])
        elif fixed:
            clauses.extend([-v] for v in vs)
        else:
            c = CardEnc.equals(vs, 1, top_id=top, encoding=EncType.seqcounter)
            top = c.nv
            clauses.extend(c.clauses)

    for y in range(n):
        exactly([lit(0, y, z) for z in range(n)])
    for z in range(n):
        exactly([lit(0, y, z) for y in range(n)])
        exactly([lit(y, 0, z) for y in range(n)])
    for x in range(n):
        for a in range(n):
            for b in range(n):
                clause([neg(lit(0, x, a)), neg(lit(0, a, b)), lit(b, 0, x)])
    # If 0 were a hole difference, F(a)=F(-2a)=0 would force 3a=0.
    # When 3 is invertible this contradicts the requirement that F(a) is defined.
    if q % 3:
        for z in range(q, n):
            clause([neg(lit(0, 0, z))])
    path = root / (name + ".cnf.gz")
    path.write_bytes(
        gzip.compress(
            (
                f"p cnf {top} {len(clauses)}\n"
                + "".join(" ".join(map(str, c)) + " 0\n" for c in clauses)
            ).encode()
        )
    )
    start = time.time()
    if args.generate_only:
        return {
            "name": name,
            "status": "GENERATED",
            "order": n,
            "cycle_length": q,
            "fixed_points": p,
            "fixed_point_shifts": list(A),
        }
    r = subprocess.run(
        ["cadical", "-t", str(args.seconds), str(path)],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=args.seconds + 15,
    )
    out = r.stdout.decode()
    (root / (name + ".log")).write_text(out)
    d = {
        "order": n,
        "cycle_length": q,
        "fixed_points": p,
        "fixed_point_shifts": list(A),
        "status": "UNRESOLVED",
        "solver_exit_code": r.returncode,
        "seconds": time.time() - start,
    }
    if r.returncode == 20:
        d["status"] = "UNSAT_FIXED_AUTOMORPHISM_AND_SHIFTS"
    elif r.returncode not in (0, 10):
        d["status"] = "SOLVER_ERROR"
    if r.returncode == 10:
        vals = {
            int(x)
            for line in out.splitlines()
            if line.startswith("v ")
            for x in line.split()[1:]
            if int(x) > 0
        }

        def true(v):
            return v if type(v) is bool else v in vals

        t = [
            [next(z for z in range(n) if true(lit(x, y, z))) for y in range(n)]
            for x in range(n)
        ]
        validate(t, n, 229)
        e63 = [[row.index(y) for y in range(n)] for row in t]
        validate(e63, n, 63)
        d.update(status="VERIFIED_MODEL_NOT_LEAN", e229_table=t, e63_table=e63)
    (root / (name + ".json")).write_text(json.dumps(d, indent=2) + "\n")
    print(index, A, d["status"], round(d["seconds"], 3), flush=True)
    return d


with ThreadPoolExecutor(max_workers=args.jobs) as pool:
    results = list(pool.map(run, enumerate(cases)))
(root / f"one-orbit-{q}-{p}-report.json").write_text(
    json.dumps(results, indent=2) + "\n"
)
