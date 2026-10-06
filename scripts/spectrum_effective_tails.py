#!/usr/bin/env python3
"""Check the effective E1083/E1286 tails (computer-assisted, not Lean certificates).

By default, check both laws, including regenerating their finite construction
bitmaps. --reuse-bitmaps checks saved bitmaps against the certified digests.
Python's standard library and a C++ compiler suffice. No model finder is needed.
"""
import argparse
import bisect
from concurrent.futures import ThreadPoolExecutor
import gzip
import hashlib
import json
import math
from pathlib import Path
import shutil
import subprocess

from spectrum_effective_bound import polynomial_operations, require

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data/spectrum"


def sha256_file(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024*1024), b""):
            digest.update(block)
    return digest.hexdigest()


def check_gap():
    """Exact periodic counts prove a 22,000-integer gap for TD(1009,q).

    Every interval has >=4215 integers coprime to 30030. Multiples of primes
    17 through 1007 account for at most 4202 of those. A surviving integer has
    no prime divisor <=1008, so the cyclic-ring transversal construction works.
    """
    wheel, gap = 30030, 22000
    coprime = [int(math.gcd(i, wheel) == 1) for i in range(wheel)]
    phi = sum(coprime)
    cache = {}

    def limits(length):
        turns, remainder = divmod(length, wheel)
        if remainder not in cache:
            count = sum(coprime[:remainder])
            minimum = maximum = count
            for start in range(wheel):
                count += coprime[(start+remainder) % wheel] - coprime[start]
                minimum, maximum = min(minimum, count), max(maximum, count)
            cache[remainder] = minimum, maximum
        lo, hi = cache[remainder]
        return turns*phi+lo, turns*phi+hi

    primes = [p for p in range(2, 1009)
              if all(p % d for d in range(2, math.isqrt(p)+1))]
    lower = limits(gap)[0]
    upper = sum(limits((gap+p-1)//p)[1] for p in primes if wheel % p)
    require(lower == 4215 and upper == 4202 and lower > upper, "The TD gap sieve failed")
    return gap


def checked_seeds(certificate):
    law, bound = certificate["law"], certificate["source_bound"]
    require(law in (1083, 1286) and bound == 1000000000, "Unsupported source domain")
    minimum = 3 if law == 1083 else 7
    seeds = {}
    for n, a, b, idem in certificate["scalars"]:
        require(minimum <= n <= bound and idem in (0, 1), "Invalid scalar seed")
        first = a*b*(a+b*b) if law == 1083 else a*b*(a*a+b)
        require(first % n == 1 and (a+a*a*b*b+b*b) % n == 0, "Scalar identity failed")
        require(not idem or (a+b) % n == 1, "Scalar idempotence failed")
        seeds[n] = max(seeds.get(n, 0), idem)
    for p, modulus, left, right, idem in certificate["extensions"]:
        reduce, add, mul = polynomial_operations(p, modulus)
        a, b = reduce(left), reduce(right)
        a2, b2 = mul(a, a), mul(b, b)
        first = mul(mul(a, b), add(a, b2) if law == 1083 else add(a2, b))
        n = p ** (len(modulus)-1)
        require(minimum <= n <= bound and idem in (0, 1), "Invalid extension seed")
        require(first == (1,) and add(add(a, mul(a2, b2)), b2) == (),
                "Quotient-ring identity failed")
        require(not idem or add(a, b) == (1,), "Quotient-ring idempotence failed")
        seeds[n] = max(seeds.get(n, 0), idem)
    # Unlike E677, all exceptional small seeds here are already quotient-ring
    # recipes: 9 (idempotent), 8 for E1083, and 32 for E1286.
    require(seeds.get(9) == 1 and (8 if law == 1083 else 32) in seeds,
            "Missing small algebraic seed")
    for order in certificate.get("projective_seeds", []):
        require(order == 448, "Unsupported projective seed")
        from spectrum_binary_half_design import construct448
        # Independently reconstruct all groups/blocks and check both laws and
        # idempotence. The repository stores the construction, not a 448² table.
        construct448(certificate)
        seeds[448] = 1
    return seeds


def check_law(law, work, reuse, gap, jobs):
    with gzip.open(DATA / f"e{law}_effective_tail.json.gz", "rt") as stream:
        certificate = json.load(stream)
    require(certificate["version"] == 1 and certificate["law"] == law, "Wrong certificate")
    seeds = checked_seeds(certificate)
    cutoff, end = certificate["cutoff"], certificate["base_end"]
    require(0 < cutoff and certificate["gap"] == gap and
            1009*(cutoff+1008*gap) <= end, "Finite base does not reach the induction threshold")
    work.mkdir(parents=True, exist_ok=True)
    have, idem = (work / f"{kind}-{law}.bin" for kind in ("have", "idem"))
    if not reuse:
        seed_file = work / f"seeds-{law}.tsv"
        seed_file.write_text("".join(f"{n} {i}\n" for n, i in sorted(seeds.items())))
        command = [str(work / "closure"), str(seed_file), str(certificate["source_bound"]),
                   str(have), str(law), str(idem)]
        if certificate.get("binary_simplex_closure", False):
            require(certificate["binary_simplex_closure"] is True, "Invalid binary closure flag")
            command.append("1")
        subprocess.run(command, check=True)
    for kind, path in (("have", have), ("idem", idem)):
        require(path.stat().st_size == (certificate["source_bound"]+8)//8, "Wrong bitmap length")
        require(sha256_file(path) == certificate[f"{kind}_sha256"], "Source bitmap digest mismatch")
    covers = work / f"cover-{law}.tsv"
    with gzip.open(DATA / f"e{law}_tail_cover.tsv.gz", "rb") as source, covers.open("wb") as dest:
        shutil.copyfileobj(source, dest)
    require(sha256_file(covers) == certificate["cover_sha256"], "Cover certificate digest mismatch")
    recipes, gaps = work / f"recipes-{law}.tsv", work / f"gaps-{law}.txt"
    require(all((len(row) == 4 or (len(row) == 7 and row[1] == -2))
                and all(type(x) is int for x in row)
                for row in certificate["recipes"]), "Malformed auxiliary recipes")
    require(all(type(n) is int for n in certificate["gaps"]), "Malformed gaps")
    recipes.write_text("".join(" ".join(map(str, row))+"\n" for row in certificate["recipes"]))
    gaps.write_text("".join(f"{n}\n" for n in certificate["gaps"]))
    origin, chunk = certificate["origin"], certificate["chunk_size"]
    require(0 < origin and 0 < chunk, "Invalid finite interval parameters")
    require(cutoff >= origin or certificate.get("prefix"), "Missing finite prefix below the core interval")
    count = (end-origin)//chunk+1
    jobs = min(jobs, count)
    starts = [origin+(count*j//jobs)*chunk for j in range(jobs)]
    stops = [n-1 for n in starts[1:]]+[end]
    parts = [work / f"cover-{law}-part-{j}.tsv" for j in range(jobs)]
    streams = [path.open("w") for path in parts]
    try:
        with covers.open() as stream:
            for line in stream:
                row = [int(x) for x in line.split()]
                require(len(row) == 5 and origin <= row[0] <= end, "Invalid cover row")
                streams[bisect.bisect_right(starts, row[0])-1].write(line)
    finally:
        for stream in streams:
            stream.close()

    def replay(j):
        subprocess.run([str(work / "cover-check"), str(have), str(idem), str(parts[j]),
                        str(recipes), str(gaps), str(origin), str(max(cutoff, origin)), str(stops[j]),
                        str(chunk), str(starts[j])], check=True)

    # The exact partition above covers the entire finite interval. Each replay
    # checks only backwards dependencies, so induction combines the results.
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        list(pool.map(replay, range(jobs)))
    if cutoff < origin:
        check_prefix(certificate, work, have, idem, recipes, gaps)
    print(f"E{law}: every order n >= {cutoff:,} is constructed.", flush=True)


def check_prefix(certificate, work, have, idem, recipes, gaps):
    """Extend the already checked core interval down to a tighter cutoff."""
    prefix = certificate["prefix"]
    law, cutoff, origin = (certificate[k] for k in ("law", "cutoff", "origin"))
    require(0 < cutoff < origin and prefix["chunk_size"] > 0, "Invalid finite prefix")
    path = work / f"prefix-{law}.tsv"
    with gzip.open(DATA / f"e{law}_tail_prefix.tsv.gz", "rb") as src, path.open("wb") as dst:
        shutil.copyfileobj(src, dst)
    require(sha256_file(path) == prefix["cover_sha256"], "Prefix certificate digest mismatch")
    subprocess.run([str(work / "cover-check"), str(have), str(idem), str(path),
                    str(recipes), str(gaps), str(cutoff), str(cutoff), str(origin-1),
                    str(prefix["chunk_size"])], check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--law", type=int, choices=(1083, 1286), help="Check only this law")
    parser.add_argument("--reuse-bitmaps", action="store_true", help="Digest-check previous bitmaps")
    parser.add_argument("--jobs", type=int, choices=range(1, 9), default=1,
                        help="Replay this many disjoint ranges in parallel (1–8)")
    parser.add_argument("--workdir", type=Path, default=ROOT / ".cache/effective-tail-check")
    args = parser.parse_args()
    gap = check_gap()
    print("TD(1009,q) gap verified: 22,000 integers; 4,215 candidates versus at most 4,202 bad.", flush=True)
    args.workdir.mkdir(parents=True, exist_ok=True)
    for executable, source in (("closure", "spectrum_effective_bound.cpp"),
                               ("cover-check", "spectrum_tail_cover_check.cpp")):
        subprocess.run(["c++", "-O3", "-march=native", str(ROOT / "scripts" / source),
                        "-o", str(args.workdir / executable)], check=True)
    for law in (args.law,) if args.law else (1083, 1286):
        check_law(law, args.workdir, args.reuse_bitmaps, gap, args.jobs)
    print("Computer-assisted tails verified. The concrete certificates still await Lean checking.")


if __name__ == "__main__":
    main()
