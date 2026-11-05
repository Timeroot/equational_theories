#!/usr/bin/env python3
"""Exhaust E872 candidate countermodels with two-point congruence classes.

For a three-element division image Q, consider every operation
  (a,u)*(b,v) = (Q(a,b), v + A[a,b]*u + C[a,b]) over F2.
These are all row-bijective extensions with that quotient and those fibres.
Boolean bitsets check all 2^18 choices of A,C simultaneously. A surviving
candidate is NOT claimed to characterize the unrestricted image.
"""
import argparse
from functools import lru_cache
import itertools
import json
from pathlib import Path

from parastrophe_e872_compression import BASE, Model, core
from parastrophe_rewrite_replay import freeze


def bit_columns(bits):
    count = 1 << bits
    if count < 8:
        return [sum(((p >> i) & 1) << p for p in range(count)) for i in range(bits)]
    columns = []
    for i in range(bits):
        if i < 3:
            data = bytes([0xaa, 0xcc, 0xf0][i:i+1]) * (count // 8)
        else:
            width = (1 << i) // 8
            data = (bytes(width) + b"\xff" * width) * (count // (16 * width))
        columns.append(int.from_bytes(data, "little"))
    return columns


def parameter_masks(quotient, terms):
    """Return masks for the exact basis and each candidate x=term."""
    k = len(quotient)
    if not 1 <= k <= 3:
        raise ValueError("This exhaustive search supports quotients of size at most three")
    bits = 2 * k * k
    all_bits = (1 << (1 << bits)) - 1
    columns = bit_columns(bits)
    good, valid = all_bits, [all_bits] * len(terms)
    for xyz in itertools.product(range(k), repeat=3):
        @lru_cache(None)
        def evaluate(t):
            if isinstance(t, int):
                return xyz[t], tuple(all_bits if i == t else 0 for i in range(4))
            a, u = evaluate(t[0])
            b, v = evaluate(t[1])
            cell = k*a+b
            return quotient[a][b], tuple(
                v[i] ^ (columns[cell] & u[i]) ^ (columns[k*k+cell] if i == 3 else 0)
                for i in range(4))

        def mask(t):
            z, w = evaluate(t)
            if z != xyz[0]:
                return 0
            return w[0] & (all_bits ^ w[1]) & (all_bits ^ w[2]) & (all_bits ^ w[3])

        good &= mask((0, core(0))) & mask(BASE)
        for j, t in enumerate(terms):
            valid[j] &= mask(t)
        evaluate.cache_clear()
    return good, valid


def table(quotient, parameters):
    k = len(quotient)
    result = []
    for x in range(2*k):
        a, u = divmod(x, 2)
        row = []
        for y in range(2*k):
            b, v = divmod(y, 2)
            cell = k*a+b
            alpha = (parameters >> cell) & 1
            constant = (parameters >> (k*k+cell)) & 1
            row.append(2*quotient[a][b] + (v ^ (alpha & u) ^ constant))
        result.append(row)
    return result


def quotient_images(k=3):
    permutations = list(itertools.permutations(range(k)))
    representatives = set()
    for rows in itertools.product(permutations, repeat=k):
        if not Model([list(r) for r in rows]).is_image():
            continue
        conjugates = []
        for p in permutations:
            inv = [p.index(i) for i in range(k)]
            conjugates.append(tuple(p[rows[inv[x]][inv[y]]] for x in range(k) for y in range(k)))
        representatives.add(min(conjugates))
    return [[list(q[k*x:k*x+k]) for x in range(k)] for q in sorted(representatives)]


def replay(record):
    candidates = record["rewrite_replay"]["unresolved"]
    terms = [freeze(c["term"]) for c in candidates]
    results = []
    for quotient in quotient_images():
        good, valid = parameter_masks(quotient, terms)
        checks = []
        for candidate, t, mask in zip(candidates, terms, valid):
            bad = mask & ~good
            check = {"index": candidate["index"], "bad_parameter_count": bad.bit_count()}
            if bad:
                parameters = (bad & -bad).bit_length() - 1
                witness = table(quotient, parameters)
                model = Model(witness)
                assert model.holds(t) and not model.is_image()
                check.update(parameters=parameters, model=witness)
            checks.append(check)
        results.append({"quotient": quotient, "parameter_choices": 1 << 18,
                        "image_parameter_count": good.bit_count(), "candidates": checks})
    return {"status": "External exhaustive check of this construction family only",
            "candidate_count": len(candidates), "quotients": results}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("record", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = replay(json.loads(args.record.read_text()))
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    refuted = {c["index"] for q in result["quotients"] for c in q["candidates"]
               if c["bad_parameter_count"]}
    print(f"{len(result['quotients'])} quotient types; {len(refuted)} candidates refuted.")


if __name__ == "__main__":
    main()
