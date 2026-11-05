#!/usr/bin/env python3
"""Find E872 image counterexamples D(x,y)=(1-i)x+iy+1 with i²=-1.

Compute exact Gaussian-integer coefficients. A prime divisor of the constant
can supply a model over Fp (split primes) or Fp[i] (nonsplit primes). This is a
specific family, not an exhaustive search for defining equations.
"""
import argparse
from functools import lru_cache
import json
from pathlib import Path

from parastrophe_rewrite_replay import freeze


@lru_cache(None)
def coefficients(t):
    if isinstance(t, int):
        if t not in (0, 1, 2):
            raise ValueError("Expected a three-variable term")
        return tuple((int(j == t), 0) for j in range(4))
    u, v = map(coefficients, t)
    # (1-i)(a+bi) + i(c+di), plus 1 for the constant coefficient.
    return tuple((a+b-d+int(j == 3), b-a+c)
                 for j, ((a,b), (c,d)) in enumerate(zip(u,v)))


def prime_factors(n):
    p = 2
    while p*p <= n:
        if n % p == 0:
            yield p
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        yield n


def scan(record):
    groups = {}
    results = []
    for candidate in record["rewrite_replay"]["unresolved"]:
        cs = coefficients(freeze(candidate["term"]))
        if cs[:3] != ((1,0), (0,0), (0,0)):
            raise ValueError(f"Candidate {candidate['index']} has unexpected variable coefficients")
        a, b = cs[3]
        norm = a*a+b*b
        witness = None
        # Norm zero gives no useful finite list of primes, so leave it unresolved.
        for p in prime_factors(norm):
            if p % 4 == 3 and a % p == b % p == 0:
                witness = {"p": p, "a": [1,-1], "b": [0,1], "c": [1,0]}
                kind = "quadratic"
                break
            roots = [i for i in range(p) if (i*i+1) % p == 0
                     and (a+b*i) % p == 0 and (2*i-1) % p != 0]
            if roots:
                i = roots[0]
                witness = {"p": p, "a": (1-i) % p, "b": i, "c": 1}
                kind = "scalar"
                break
        if witness:
            key = kind, json.dumps(witness)
            groups.setdefault(key, []).append(candidate["index"])
        results.append({"index": candidate["index"], "operations": candidate["operations"],
                        "constant": [a,b], "norm": norm, "model": witness})
    return {"candidates": results, "groups": [
        {"kind": kind, "spec": json.loads(spec), "indices": indices}
        for (kind,spec), indices in groups.items()]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("record", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = scan(json.loads(args.record.read_text()))
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    count = sum(c["model"] is not None for c in result["candidates"])
    print(f"{count} refuted; {len(result['candidates'])-count} survivors of this family.")


if __name__ == "__main__":
    main()
