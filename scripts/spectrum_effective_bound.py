#!/usr/bin/env python3
"""Reproduce the computer-assisted E677 bound; this is not a Lean certificate.

The normal invocation checks all algebraic seed identities, recomputes the
positive construction closure in C++, and checks the finite weighted sieve and
induction hypotheses. --bitmap checks a previously computed bitmap against the
saved digest instead of recomputing it. No optimizer is needed for checking.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import subprocess

ROOT = Path(__file__).resolve().parents[1]
CERTIFICATE = ROOT / "data/spectrum/e677_effective_bound.json.gz"
PRIMES = [p for p in range(5, 81) if all(p % d for d in range(2, int(p**0.5) + 1))]
TABLE9 = [
    [0, 5, 7, 8, 1, 3, 4, 6, 2], [1, 3, 8, 6, 2, 4, 5, 7, 0],
    [2, 4, 6, 7, 0, 5, 3, 8, 1], [3, 8, 1, 2, 4, 6, 7, 0, 5],
    [4, 6, 2, 0, 5, 7, 8, 1, 3], [5, 7, 0, 1, 3, 8, 6, 2, 4],
    [6, 2, 4, 5, 7, 0, 1, 3, 8], [7, 0, 5, 3, 8, 1, 2, 4, 6],
    [8, 1, 3, 4, 6, 2, 0, 5, 7],
]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def polynomial_operations(p, modulus):
    """Arithmetic in (Z/p)[X]/(monic modulus), using coefficient lists."""
    require(p >= 2 and len(modulus) >= 2 and modulus[-1] == 1, "Invalid quotient ring")
    require(all(type(c) is int and 0 <= c < p for c in modulus), "Invalid coefficients")
    degree = len(modulus) - 1

    def reduce(coefficients):
        values = [int(c) % p for c in coefficients]
        while len(values) > degree:
            lead = values[-1]
            offset = len(values) - 1 - degree
            for j, coefficient in enumerate(modulus):
                values[offset + j] = (values[offset + j] - lead * coefficient) % p
            values.pop()
        while values and not values[-1]:
            values.pop()
        return tuple(values)

    def add(a, b):
        values = [0] * max(len(a), len(b))
        for i, c in enumerate(a):
            values[i] += c
        for i, c in enumerate(b):
            values[i] += c
        return reduce(values)

    def mul(a, b):
        values = [0] * (len(a) + len(b))
        for i, c in enumerate(a):
            for j, d in enumerate(b):
                values[i + j] += c*d
        return reduce(values)

    return reduce, add, mul


def checked_seeds(certificate):
    seeds = {}
    bound = certificate["base_end"]
    for n, a, b, idem in certificate["scalars"]:
        require(5 <= n <= bound and idem in (0, 1), "Invalid scalar seed")
        require((a*b + a*b**3) % n == 1 and (a + a*a*b*b + b**3) % n == 0,
                f"E677 scalar identity fails at {n}")
        require(not idem or (a+b) % n == 1, f"Idempotence fails at {n}")
        seeds[n] = max(seeds.get(n, 0), idem)
    for p, modulus, coefficients, idem in certificate["extensions"]:
        reduce, add, mul = polynomial_operations(p, modulus)
        a, b = reduce(coefficients), reduce([0, 1])
        b2 = mul(b, b)
        b3 = mul(b2, b)
        n = p ** (len(modulus) - 1)
        require(5 <= n <= bound and idem in (0, 1), "Invalid extension seed")
        require(add(mul(a, b), mul(a, b3)) == (1,), f"First quotient-ring identity fails at {n}")
        require(add(add(a, mul(mul(a, a), b2)), b3) == (),
                f"Second quotient-ring identity fails at {n}")
        require(not idem or add(a, b) == (1,), f"Quotient-ring idempotence fails at {n}")
        seeds[n] = max(seeds.get(n, 0), idem)
    require(TABLE9[0][0] == 0, "The nine-element seed is not pointed")
    for x in range(9):
        for y in range(9):
            require(TABLE9[y][TABLE9[x][TABLE9[TABLE9[y][x]][y]]] == x,
                    "The nine-element seed fails E677")
    return seeds


def checked_sieve(certificate):
    sieve = certificate["sieve"]
    require(sieve["step"] == 480 and sieve["R"] == certificate["hole_bound"], "Wrong sieve parameters")
    require(sieve["primes"] == PRIMES, "Wrong sieve primes")
    require([row["residue"] for row in sieve["rows"]] == list(range(480)), "Missing residue class")
    orders = set()
    for row in sieve["rows"]:
        indices, weights = row["indices"], row["weights"]
        require(len(indices) == len(weights) and len(set(indices)) == len(indices), "Invalid sieve indices")
        require(all(type(j) is int and j >= 0 for j in indices), "Invalid sieve index")
        require(all(type(w) is int and w > 0 for w in weights), "Invalid sieve weight")
        caps = []
        for p in PRIMES:
            buckets = [0] * p
            for j, w in zip(indices, weights):
                buckets[j % p] += w
            caps.append(max(buckets))
        require(caps == row["caps"] and sum(caps) < sum(weights),
                f"Weighted sieve fails in residue {row['residue']}")
        for j in indices:
            n = 480*j + row["residue"]
            require(0 < n <= certificate["hole_bound"], "Hole is outside the certified bound")
            orders.add(n)
    return orders


def member(bitmap, n):
    return bool(bitmap[n // 8] & (1 << (n % 8)))


def interval(bitmap, lo, hi, odd_only=False):
    """Check an interval without allocating its list of individual orders."""
    while lo <= hi and lo % 8:
        require(odd_only and lo % 2 == 0 or member(bitmap, lo), f"Missing order {lo}")
        lo += 1
    while lo <= hi and hi % 8 != 7:
        require(odd_only and hi % 2 == 0 or member(bitmap, hi), f"Missing order {hi}")
        hi -= 1
    if lo > hi:
        return
    block = bitmap[lo // 8: hi // 8 + 1]
    if odd_only:
        bad = block.translate(bytes(int((b & 0xAA) != 0xAA) for b in range(256)))
        require(bad.count(b"\x01") == 0, "An odd order in the required interval is missing")
    else:
        require(block.count(b"\xff") == len(block), "The finite base interval has a gap")


def check_bitmap(certificate, bitmap, holes):
    bound, cutoff, radius = (certificate[k] for k in ("base_end", "cutoff", "hole_bound"))
    bitmap = bitmap[:(bound + 8) // 8]
    require(len(bitmap) == (bound + 8) // 8, "Truncated construction bitmap")
    require(hashlib.sha256(bitmap).hexdigest() == certificate["bitmap_sha256"], "Construction bitmap digest mismatch")
    require(480 <= radius < cutoff <= 81*radius <= bound, "Invalid induction thresholds")
    interval(bitmap, cutoff, bound)
    interval(bitmap, radius, cutoff - 1, odd_only=True)
    require(not member(bitmap, cutoff - 1), "The stored cutoff is not the computed last gap plus one")
    require(all(member(bitmap, n) for n in holes), "A sieve hole lacks a construction")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path, default=CERTIFICATE)
    parser.add_argument("--bitmap", type=Path, help="Use an existing bitmap after checking its digest")
    parser.add_argument("--workdir", type=Path, default=ROOT / ".cache/effective-bound-check")
    args = parser.parse_args()
    with gzip.open(args.certificate, "rt") as stream:
        certificate = json.load(stream)
    require(certificate["version"] == 1 and certificate["law"] == 677, "Unsupported certificate")
    seeds = checked_seeds(certificate)
    holes = checked_sieve(certificate)
    print(f"Algebraic seeds and all 480 integer-weighted sieve rows checked ({len(holes):,} holes).", flush=True)
    bitmap = args.bitmap
    if bitmap is None:
        args.workdir.mkdir(parents=True, exist_ok=True)
        seed_file = args.workdir / "seeds.tsv"
        seed_file.write_text("".join(f"{n} {idem}\n" for n, idem in sorted(seeds.items())))
        executable = args.workdir / "closure"
        subprocess.run(["c++", "-O3", "-march=native", "-o", str(executable),
                        str(ROOT / "scripts/spectrum_effective_bound.cpp")], check=True)
        bitmap = args.workdir / "orders.bin"
        subprocess.run([str(executable), str(seed_file), str(certificate["base_end"]), str(bitmap)], check=True)
    check_bitmap(certificate, bitmap.read_bytes(), holes)
    print(f"E677: every order n >= {certificate['cutoff']:,} is constructed.")
    print("Computer-assisted bound verified; the finite certificates have not yet been checked in Lean.")


if __name__ == "__main__":
    main()
