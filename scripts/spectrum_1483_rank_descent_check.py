#!/usr/bin/env python3
"""Verify the saved counterexample and sample the explicitly unproved candidates."""
import itertools
import json
from pathlib import Path


def check():
    root = Path(__file__).resolve().parents[1]
    data = json.loads((root / "data/spectrum/1483_rank_descent_followup.json").read_text())
    contexts = 0
    paths = 0
    for entry in data["models"]:
        original = entry["table"]
        for opposite in (False, True):
            m = list(map(list, zip(*original))) if opposite else original
            n = len(m)
            rows = [set(row) for row in m]
            assert all(m[m[y][x]][m[x][m[y][z]]] == x
                       for x, y, z in itertools.product(range(n), repeat=3))
            for e in range(n):
                for a in rows[e]:
                    for b in rows[a]:
                        paths += 1
                        t = m[e][b]
                        assert b in rows[t]
                        F = lambda y: m[a][m[y][t]]
                        J = lambda x: m[t][m[x][t]]
                        assert len({F(y) for y in rows[t]}) == len(rows[t])
                        assert F(b) != b or a == t
                        assert t == a or len(rows[t]) < len(rows[a])
                        for q in rows[t]:
                            contexts += 1
                            assert m[t][m[q][a]] == q
                            assert m[m[a][m[q][t]]][t] == m[q][t]
                            assert J(F(q)) == q
                            c = m[m[m[m[b][a]][q]][e]][a]
                            assert m[c][q] == t
            print(f"{entry['label']}{' opposite' if opposite else ''}: checked")

    m = data["models"][-1]["table"]
    witness = data["retraction_counterexample"]
    e, a, b, t = (witness[k] for k in ("e", "a", "b", "t"))
    assert m[e][2] == a and m[a][6] == b and m[e][b] == t
    F = lambda y: m[a][m[y][t]]
    G = lambda x: m[t][m[x][a]]
    row = sorted(set(m[t]))
    assert row == witness["row_t"]
    assert [F(y) for y in row] == witness["F_on_row_t"]
    assert [G(F(y)) for y in row] == witness["GF_on_row_t"]
    assert len({G(F(y)) for y in row}) < len(row)
    print(f"Verified GF counterexample; sampled {paths} paths and {contexts} row elements.")
    print("Passing sample checks do not prove any general candidate identity.")


if __name__ == "__main__":
    check()
