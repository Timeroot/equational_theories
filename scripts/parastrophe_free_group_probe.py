#!/usr/bin/env python3
"""Experimental E464 free-group completion, not a proof of an infinite model.

Represent reduced free words by tuples of signed generator names. For
x ◇ y = x f(x⁻¹y), E464 asks for f(x⁻¹ f³(x)) = x⁻¹. Starting from a
five-pair collision seed, extend f at selected missing inputs with a fresh
generator, close under this equation, and check proposed extension invariants.

The scheduler explores inverses/images and some initial short words. It does
NOT enumerate the entire free group. Even indefinitely successful finite
runs would still require an extension proof and exhaustive scheduling.
This script is research scratch and has no role in Lean or website exports.
"""
import argparse
import heapq
import itertools
import json
import random
import time


def mul(a, b):
    s = list(a)
    for x in b:
        if s and s[-1] == -x:
            s.pop()
        else:
            s.append(x)
    return tuple(s)


def inv(x):
    return tuple(-i for i in x[::-1])


def expand(n, steps=500, seed=0):
    if n != 3:
        raise ValueError("The auxiliary invariants in this probe are for E464 (n=3).")
    rng = random.Random(seed)
    f = {(): (), (1,): (3,), (2,): (3,), (-4,): (-4, 6), (-5,): (-5, 6)}
    fresh = 20
    history = []
    pending = []
    counter = itertools.count()
    queued = set()

    def push(x):
        x = mul((), x)
        if x not in queued:
            queued.add(x)
            heapq.heappush(
                pending, (sum(map(abs, x)) + len(x) + rng.random(), next(counter), x)
            )

    for x in [
        *((i,) for i in range(-6, 7) if i),
        *(tuple(x) for x in itertools.product([1, 2, -1, -2], repeat=2)),
    ]:
        push(x)
    start = time.monotonic()

    def closure():
        todo = list(f)
        scans = 0
        while todo:
            x = todo.pop()
            v = x
            for _ in range(n):
                if v not in f:
                    break
                v = f[v]
            else:
                a, b = mul(inv(x), v), inv(x)
                if a in f:
                    if f[a] != b:
                        return {"conflict": [x, a, f[a], b]}
                else:
                    f[a] = b
                    todo = list(f)
                    scans += 1
                    if scans > 5000:
                        return {"extension_budget_exhausted": len(f)}
        return None

    for t in range(steps):
        while pending and pending[0][2] in f:
            heapq.heappop(pending)
        if not pending:
            for x in f:
                push(inv(x))
                push(f[x])
        if not pending:
            return {"stopped": t}
        _, _, d = heapq.heappop(pending)
        c = (fresh,)
        fresh += 1
        old = dict(f)
        f[d] = c
        # The proposed extension has the same two forced families as E63,
        # replacing old one-step paths by old (n-1)-step paths.
        power = {}
        for x in old:
            v = x
            for _ in range(n - 1):
                if v not in old:
                    break
                v = old[v]
            else:
                power[x] = v
        predicted = {d: c}
        for h, v in power.items():
            if v == d:
                predicted[mul(inv(h), c)] = inv(h)
                if inv(h) in power:
                    predicted[mul(mul(inv(c), h), power[inv(h)])] = mul(inv(c), h)
        problem = closure()
        if not problem:
            actual = {x: y for x, y in f.items() if x not in old}
            if actual != predicted:
                return {
                    "n": n,
                    "seed": seed,
                    "step": t,
                    "extension_mismatch": {
                        "d": d,
                        "predicted": list(predicted.items()),
                        "actual": list(actual.items()),
                    },
                }
        if not problem:
            power = {x: f[f[x]] for x in f if f[x] in f}
            groups = {}
            for x, y in power.items():
                groups.setdefault(y, []).append(x)
            for x, y in power.items():
                if y == inv(x) and x:
                    return {"n": n, "step": t, "aux2_failure": [x, y]}
                if inv(x) in power:
                    z = power[inv(x)]
                    for xp in groups[y]:
                        if xp != x and xp == mul(x, z):
                            return {"n": n, "step": t, "aux3_failure": [x, xp, z]}
                        if (
                            xp != x
                            and inv(xp) in power
                            and mul(xp, power[inv(xp)]) == mul(x, z)
                        ):
                            return {
                                "n": n,
                                "step": t,
                                "aux4_failure": [x, xp, z, power[inv(xp)]],
                            }

        history.append([d, len(f) - len(old)])
        if problem:
            return {
                "n": n,
                "seed": seed,
                "step": t,
                "pairs": len(f),
                "problem": problem,
                "last": history[-10:],
            }
        # Explore inverses and images before exhausting the short original words.
        for x in f.keys() - old.keys():
            push(inv(x))
            push(f[x])
        if t % 100 == 0:
            print(
                "progress",
                n,
                seed,
                t,
                len(f),
                round(time.monotonic() - start, 1),
                flush=True,
            )
    return {
        "n": n,
        "seed": seed,
        "steps": steps,
        "pairs": len(f),
        "maxAdded": max(x[1] for x in history),
        "maxWordLength": max(map(len, f)),
        "seconds": round(time.monotonic() - start, 1),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--steps", type=int, default=2000)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    if args.steps < 1:
        parser.error("--steps must be positive")
    print(json.dumps(expand(3, args.steps, args.seed), indent=2))
