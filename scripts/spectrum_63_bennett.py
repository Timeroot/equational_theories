#!/usr/bin/env python3
"""Rebuild explicit E63 models from constructions in Bennett (1989).

Uses only the Python standard library. Every generated table is checked
against Latinness, E229, and its row-inverse E63 presentation. These checks
are not proof oracles. Separate Lean proofs now establish existence at all
twelve orders, with six of these exact tables checked by the kernel. The small 23-point GDD is independently checked here;
its discovery solver is not needed to replay the certificate.
"""
import argparse
import hashlib
import json
from pathlib import Path
from itertools import combinations
from spectrum_63_atp import validate

ROOT = Path(__file__).resolve().parent.parent


def prime(n, idem=True):
    b = next(
        b for b in range(1, n) if (b**3 - b + 1 if idem else b**5 + b**4 + 1) % n == 0
    )
    return [[(b * b * x + pow(b, -1, n) * y) % n for y in range(n)] for x in range(n)]


def gf_mul(a, b, mod):
    out = 0
    q = 1 << (mod.bit_length() - 1)
    while b:
        if b & 1:
            out ^= a
        b >>= 1
        a <<= 1
        if a & q:
            a ^= mod
    return out


def gf_affine(q, mod, a, b):
    return [[gf_mul(a, x, mod) ^ gf_mul(b, y, mod) for y in range(q)] for x in range(q)]


def product(a, b):
    n, m = len(a), len(b)
    return [
        [a[x // m][y // m] * m + b[x % m][y % m] for y in range(n * m)]
        for x in range(n * m)
    ]


def singular(v, q, b, p=1):
    nv, nq, nb = len(v), len(q), len(b)
    assert nb == nq - p
    assert all(v[x][x] == x for x in range(nv))
    assert all(q[x][y] < p for x in range(p) for y in range(p))
    points = [(None, x) for x in range(p)] + [
        (i, a) for i in range(nv) for a in range(p, nq)
    ]
    index = {x: i for i, x in enumerate(points)}

    def f(X, Y):
        i, a = X
        j, c = Y
        if i is None or j is None or i == j:
            k = i if j is None else j
            z = q[a][c]
            return index[(None, z) if z < p else (k, z)]
        return index[(v[i][j], p + b[a - p][c - p])]

    return [[f(x, y) for y in points] for x in points]


def add(q, x, y):
    if q == 8:
        return x ^ y
    if q == 9:
        return (x % 3 + y % 3) % 3 + 3 * ((x // 3 + y // 3) % 3)
    return (x + y) % q


def mul(q, x, y):
    if q == 8:
        return gf_mul(x, y, 11)
    if q == 9:
        a, b = x % 3, x // 3
        c, d = y % 3, y // 3
        return (a * c - b * d) % 3 + 3 * ((a * d + b * c) % 3)
    return x * y % q


def td(q, k):
    groups = [[i * q + j for j in range(q)] for i in range(k)]
    blocks = [
        [i * q + (b if i == q else add(q, a, mul(q, i, b))) for i in range(k)]
        for a in range(q)
        for b in range(q)
    ]
    return groups, blocks


def restrict(groups, blocks, removed):
    return [[x for x in g if x not in removed] for g in groups], [
        [x for x in b if x not in removed] for b in blocks
    ]


def glue(groups, blocks, p, fillers, block_tables):
    pts = sorted(set(sum(groups, [])))
    n = len(pts) + p
    idx = {x: p + i for i, x in enumerate(pts)}
    result = [[-1] * n for _ in range(n)]
    common = list(range(p))
    covered = set()
    for g, f in zip(groups, fillers):
        mapping = common + [idx[x] for x in g]
        assert len(mapping) == len(f)
        for a in range(len(mapping)):
            for b in range(len(mapping)):
                if a < p and b < p:
                    continue
                x, y = mapping[a], mapping[b]
                assert result[x][y] == -1
                result[x][y] = mapping[f[a][b]]
    for b in blocks:
        if len(b) < 2:
            continue
        local = block_tables[len(b)]
        assert all(local[x][x] == x for x in range(len(b)))
        for x, y in combinations(b, 2):
            assert (min(x, y), max(x, y)) not in covered
            covered.add((min(x, y), max(x, y)))
        for a, x in enumerate(b):
            for c, y in enumerate(b):
                if x == y:
                    continue
                X, Y = idx[x], idx[y]
                assert result[X][Y] == -1
                result[X][Y] = idx[b[local[a][c]]]
    # The last filling determines the common part; its p points need not form a subquasigroup.
    mapping = common + [idx[x] for x in groups[-1]]
    last = fillers[-1]
    for x in range(p):
        for y in range(p):
            result[x][y] = mapping[last[x][y]]
    assert all(z >= 0 for row in result for z in row)
    validate(result, n, 229)
    return result


def build():
    tables = {
        3: prime(3, False),
        4: gf_affine(4, 7, 2, 2),
        5: prime(5),
        7: prime(7),
        8: gf_affine(8, 11, 4, 5),
        11: prime(11),
        19: prime(19),
    }
    for n, t in tables.items():
        validate(t, n, 229)
    for n, a, q, b in [(22, 7, 4, 3), (29, 7, 5, 4), (34, 11, 4, 3), (58, 19, 4, 3)]:
        tables[n] = singular(tables[a], tables[q], tables[b])
        validate(tables[n], n, 229)
        print("VERIFIED", n, flush=True)
    tables[15] = product(tables[3], tables[5])
    tables[16] = product(tables[4], tables[4])
    tables[106] = singular(tables[7], tables[16], tables[15])
    tables[110] = product(tables[22], tables[5])
    for n in [106, 110]:
        validate(tables[n], n, 229)
        print("VERIFIED", n, flush=True)
    tables[9] = product(tables[3], tables[3])
    tables[12] = product(tables[4], tables[3])
    tables[13] = prime(13, False)
    tables[23] = prime(23)
    # 62: remove three points of one block in TD(8,8), then adjoin one common point.
    g, b = td(8, 8)
    g, b = restrict(g, b, {0, 8, 16})
    tables[62] = glue(g, b, 1, [tables[len(x) + 1] for x in g], tables)
    print("VERIFIED 62", flush=True)
    # 74: seven 9-point groups with 3 common points, plus an 8-point final group.
    g, b = td(9, 8)
    g, b = restrict(g, b, {7 * 9 + 8})
    tables[74] = glue(g, b, 3, [tables[12]] * 7 + [tables[11]], tables)
    print("VERIFIED 74", flush=True)
    # 114: remove one point from TD(5,23), regarding the lines through it as groups.
    g, b = td(23, 5)
    deleted = 0
    newgroups = [
        [x for x in block if x != deleted] for block in b if deleted in block
    ] + [[x for x in g[0] if x != deleted]]
    newblocks = [block for block in b if deleted not in block] + g[1:]
    tables[114] = glue(
        newgroups, newblocks, 0, [tables[len(x)] for x in newgroups], tables
    )
    print("VERIFIED 114", flush=True)
    # 118: the same deletion in TD(5,8), followed by a threefold lift.
    g, b = td(8, 5)
    deleted = 0
    g = [[x for x in block if x != deleted] for block in b if deleted in block] + [
        [x for x in g[0] if x != deleted]
    ]
    b = [block for block in b if deleted not in block] + td(8, 5)[0][1:]
    # On a lifted transversal use idempotent E229 on its index and an arbitrary 3-model on coordinates.
    pts = sorted(set(sum(g, [])))
    ix = {x: i for i, x in enumerate(pts)}
    N = 3 * len(pts) + 1
    tab = [[-1] * N for _ in range(N)]
    for gi in g:
        f = tables[3 * len(gi) + 1]
        mp = [0] + [1 + 3 * ix[x] + a for x in gi for a in range(3)]
        for x in range(len(mp)):
            for y in range(len(mp)):
                if x == y == 0:
                    continue
                assert tab[mp[x]][mp[y]] == -1
                tab[mp[x]][mp[y]] = mp[f[x][y]]
    for block in b:
        f = tables[len(block)]
        for a, x in enumerate(block):
            for c, y in enumerate(block):
                if x == y:
                    continue
                z = block[f[a][c]]
                for i in range(3):
                    for j in range(3):
                        X = 1 + 3 * ix[x] + i
                        Y = 1 + 3 * ix[y] + j
                        assert tab[X][Y] == -1
                        tab[X][Y] = 1 + 3 * ix[z] + tables[3][i][j]
    tab[0][0] = 0
    validate(tab, 118, 229)
    tables[118] = tab
    print("VERIFIED 118", flush=True)
    D = json.loads((ROOT / "data/spectrum/63_bennett_gdd23.json").read_text())
    groups, blocks = D["groups"], D["blocks"]
    assert sorted(sum(groups, [])) == list(range(23))
    owner = {x: i for i, g in enumerate(groups) for x in g}
    assert sorted(map(len, groups)) == [2] * 9 + [5]
    assert all(len(b) == 4 and len({owner[x] for x in b}) == 4 for b in blocks)
    assert all(
        sum(set(pair) <= set(b) for b in blocks) == 1
        for pair in combinations(range(23), 2)
        if owner[pair[0]] != owner[pair[1]]
    )
    h = [
        [None, 7, 3, 5, None, 2, 1, 6],
        [7, None, 0, 4, 6, None, 3, 2],
        [3, 0, None, 1, 5, 7, None, 4],
        [5, 4, 1, None, 2, 6, 0, None],
        [None, 6, 5, 2, None, 3, 7, 1],
        [2, None, 7, 6, 3, None, 4, 0],
        [1, 3, None, 0, 7, 4, None, 5],
        [6, 2, 4, None, 1, 0, 5, None],
    ]
    for x in range(8):
        for y in range(8):
            if x % 4 != y % 4:
                assert h[h[y][h[y][x]]][y] == x
    n = 47
    t = [[-1] * n for _ in range(n)]
    for g in groups:
        f = tables[2 * len(g) + 1]
        mp = [0] + [1 + 2 * x + i for x in g for i in range(2)]
        for x in range(len(mp)):
            for y in range(len(mp)):
                if x == y == 0:
                    continue
                assert t[mp[x]][mp[y]] == -1
                t[mp[x]][mp[y]] = mp[f[x][y]]
    for b in blocks:
        for x in range(8):
            for y in range(8):
                if x % 4 == y % 4:
                    continue
                X = 1 + 2 * b[x % 4] + x // 4
                Y = 1 + 2 * b[y % 4] + y // 4
                z = h[x][y]
                assert t[X][Y] == -1
                t[X][Y] = 1 + 2 * b[z % 4] + z // 4
    t[0][0] = 0
    validate(t, 47, 229)
    tables[47] = t
    print("VERIFIED 47", flush=True)
    design = json.loads((ROOT / "data/spectrum/63_bennett_gdd46.json").read_text())
    groups, blocks = design["groups"], design["blocks"]
    assert sorted(sum(groups, [])) == list(range(46))
    owner = {x: i for i, g in enumerate(groups) for x in g}
    assert sorted(map(len, groups)) == [1] * 42 + [4]
    assert all(
        len(b) in [5, 7, 8] and len({owner[x] for x in b}) == len(b) for b in blocks
    )
    assert all(
        sum(set(pair) <= set(b) for b in blocks) == 1
        for pair in combinations(range(46), 2)
        if owner[pair[0]] != owner[pair[1]]
    )
    tables[1] = [[0]]
    tables[46] = glue(groups, blocks, 0, [tables[len(g)] for g in groups], tables)
    print("VERIFIED 46", flush=True)
    return tables


RECIPES = {
    22: "Singular product: 7*(4-1)+1; factors 7,4,3",
    29: "Singular product: 7*(5-1)+1; factors 7,5,4",
    34: "Singular product: 11*(4-1)+1; factors 11,4,3",
    46: "Checked {5,7,8}-GDD of type 1^42 4^1, constructed from a partial difference matrix over Z/7Z; fill the four-point group",
    47: "Double the checked 4-GDD of type 2^9 5^1 using the 2^4 incomplete C3 table, then fill with 5 and 11 at a common point",
    58: "Singular product: 19*(4-1)+1; factors 19,4,3",
    62: "Delete three points of one block of TD(8,8), then fill enlarged groups by 8 and 9",
    74: "TD(8,9) with one point removed from its last group; seven 12-models share a 3-hole, then fill the last enlarged group with 11",
    106: "Singular product: 7*(16-1)+1; factors 7,16,15",
    110: "Direct product 22*5",
    114: "Delete one point of TD(5,23), use its incident blocks as groups, then fill by 4 and 22",
    118: "Delete one point of TD(5,8), triple every point, then fill enlarged groups by 13 and 22",
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--write", action="store_true", help="Write the compact construction manifest"
    )
    parser.add_argument(
        "--tables", type=Path, help="Optionally write the complete E63 tables"
    )
    args = parser.parse_args()
    tables = build()
    records = []
    output = {}
    for n, recipe in sorted(RECIPES.items()):
        q = tables[n]
        validate(q, n, 229)
        t = [[row.index(y) for y in range(n)] for row in q]
        validate(t, n)
        output[str(n)] = t
        digest = hashlib.sha256(
            json.dumps(t, separators=(",", ":")).encode()
        ).hexdigest()
        records.append(
            {
                "order": n,
                "status": (
                    "LEAN_TABLE_VERIFIED"
                    if n in {46, 47, 62, 74, 114, 118}
                    else "LEAN_EXISTENCE_PROVED_TABLE_COMPUTER_CHECKED"
                ),
                "lean_existence_theorem": f"Spectrum.E63.model{n}",
                "lean_table_theorem": (
                    f"Spectrum.E63.law{n}" if n in {46, 47, 62, 74, 114, 118} else None
                ),
                "construction": recipe,
                "e63_table_sha256": digest,
                "idempotents": [x for x in range(n) if t[x][x] == x],
            }
        )
    data = {
        "law": 63,
        "status": "LEAN_EXISTENCE_PROVED",
        "source": {
            "author": "F. E. Bennett",
            "title": "Quasigroup Identities and Mendelsohn Designs",
            "year": 1989,
            "doi": "10.4153/CJM-1989-017-0",
            "theorem": "5.50",
            "published_excluded_orders": [2, 6],
            "published_unsettled_orders": [10, 14, 18, 26, 30, 38, 42, 158],
        },
        "models": records,
        "generator": "scripts/spectrum_63_bennett.py",
    }
    path = ROOT / "data/spectrum/63_bennett_constructions.json"
    if args.write:
        path.write_text(json.dumps(data, indent=2) + "\n")
    else:
        assert json.loads(path.read_text()) == data
    if args.tables:
        args.tables.write_text(json.dumps(output, indent=2) + "\n")
    print("All", len(records), "new E63 construction certificates verified.")


if __name__ == "__main__":
    main()
