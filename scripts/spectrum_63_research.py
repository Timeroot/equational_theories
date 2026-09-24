#!/usr/bin/env python3
"""Check the constructive E63 research certificate (not a Lean proof).

The mathematical construction rules and the induction past the finite
certificate are explained in docs/63_spectrum_progress.md. This checker uses
only Python's standard library and does not trust the discovery solvers.
"""
import hashlib
import json
from functools import cache
from itertools import combinations
from math import gcd, prod
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


@cache
def factors(n):
    result = []
    p = 2
    while p * p <= n:
        a = 0
        while n % p == 0:
            n //= p
            a += 1
        if a:
            result.append((p, a))
        p += 1
    if n > 1:
        result.append((n, 1))
    return tuple(result)


@cache
def cubic_root(p):
    return any((b**3 - b + 1) % p == 0 for b in range(p))


@cache
def general_root(p):
    return any((b**5 + b**4 + 1) % p == 0 for b in range(p))


def check_difference_matrices():
    data = json.loads((ROOT / "data/spectrum/63_difference_matrices.json").read_text())
    designs = {}
    for order, entry in data["matrices"].items():
        q = int(order)
        moduli, columns, rows = (
            entry[key] for key in ["group_moduli", "columns", "rows"]
        )
        assert all(m > 1 for m in moduli) and prod(moduli) == q
        assert len(rows) == q
        for row in rows:
            assert len(row) == columns
            for value in row:
                assert len(value) == len(moduli)
                assert all(0 <= x < m for x, m in zip(value, moduli))
        for i, j in combinations(range(columns), 2):
            differences = {
                tuple((a - b) % m for a, b, m in zip(row[i], row[j], moduli))
                for row in rows
            }
            assert len(differences) == q
        # Develop by adding every group element, and append the matrix-row
        # index as an extra coordinate. This gives an OA(columns+1,q).
        designs[q] = columns + 1
    return designs


def check_certificate(data, extra_designs):
    assert data["status"] == "COMPUTER_CHECKED_NOT_LEAN"
    assert data["law"] == 63
    done = {"idempotent": set(), "pointed": set()}
    nodes = {mode: {int(n): node for n, node in data[mode].items()} for mode in done}

    def td_size(q):
        return max(min(p**a for p, a in factors(q)) + 1, extra_designs.get(q, 0))

    for mode in ["idempotent", "pointed"]:
        for n, node in sorted(nodes[mode].items()):
            kind = node["kind"]
            if kind == "empty":
                assert n == 0
            elif kind == "one":
                assert n == 1
            elif kind == "affine":
                assert n > 0
                if mode == "idempotent":
                    assert all(cubic_root(p) or a % 3 == 0 for p, a in factors(n))
                else:
                    assert all(general_root(p) or a >= 2 for p, a in factors(n))
            elif kind == "idem":
                assert mode == "pointed"
                assert node["n"] == n and n in done["idempotent"]
            elif kind == "product":
                a, b = node["a"], node["b"]
                assert 1 < a < n and 1 < b < n and a * b == n
                assert a in done[mode] and b in done[mode]
            elif kind == "td":
                q, k, r, s, e = (node[key] for key in ["q", "k", "r", "s", "e"])
                assert q >= 2 and k >= 2 and e in [0, 1]
                assert 0 <= r <= q and 0 <= s <= q
                assert n == k * q + r + s + e
                for group_size in [q + e, r + e, s + e]:
                    assert group_size < n and group_size in done[mode]
                groups = k + (r > 0) + (s > 0)
                assert groups <= td_size(q)
                assert all(j in done["idempotent"] for j in range(k, groups + 1))
            elif kind == "singular_product":
                h, m, k = (node[key] for key in ["h", "m", "k"])
                assert 0 < h < n and 1 < m < n and k >= 2
                q = h * (m - 1)
                assert q >= 2 and n == k * q + h and k <= td_size(q)
                assert h in done[mode] and m in done[mode]
                assert k in done["idempotent"]
            else:
                raise AssertionError(f"Unknown construction rule: {kind}")
            done[mode].add(n)

    cutoff, induction_start = data["cutoff"], data["induction_start"]
    assert cutoff > 0 and induction_start >= 8 * (cutoff + 42)
    assert all(n in done["pointed"] for n in range(cutoff, induction_start))
    assert {7, 8} <= done["idempotent"]
    # Every interval of six consecutive integers contains an integer coprime
    # to 30. Applied to ceil(n/8), this is the only arithmetic step of induction.
    assert all(any(gcd(a + d, 30) == 1 for d in range(6)) for a in range(30))
    missing = [n for n in range(1, cutoff) if n not in done["pointed"]]
    assert missing == data["missing_below_cutoff"]
    return done, missing


def check_order_41():
    """Independently evaluate the gluing construction with non-idempotent groups."""

    # F8 = F2[t]/(t^3+t+1), using polynomial bits.
    def mul(a, b):
        result = 0
        while b:
            if b & 1:
                result ^= a
            b >>= 1
            a <<= 1
            if a & 8:
                a ^= 11
        return result

    inverse = {a: next(b for b in range(1, 8) if mul(a, b) == 1) for a in range(1, 8)}

    def op(x, y):
        if x == y == 0:
            return 0
        if x == 0 or y == 0 or (x - 1) // 8 == (y - 1) // 8:
            group = ((y if x == 0 else x) - 1) // 8
            a = 0 if x == 0 else (x - 1) % 8 + 1
            b = 0 if y == 0 else (y - 1) % 8 + 1
            # Each group plus 0 is F3^2, with a diamond b = b-a.
            c = (b % 3 - a % 3) % 3 + 3 * ((b // 3 - a // 3) % 3)
            return 0 if c == 0 else 8 * group + c
        g, u = divmod(x - 1, 8)
        h, v = divmod(y - 1, 8)
        slope = mul(u ^ v, inverse[g ^ h])
        intercept = u ^ mul(g, slope)
        # On each transversal use i diamond j = 3(i+j) mod 5.
        t = 3 * (g + h) % 5
        return 1 + 8 * t + (intercept ^ mul(t, slope))

    for x in range(41):
        assert op(x, x) == 0
        assert len({op(x, y) for y in range(41)}) == 41
        assert len({op(y, x) for y in range(41)}) == 41
        for y in range(41):
            assert op(y, op(x, op(x, y))) == x


def check_singular_examples():
    """Evaluate the new examples at 87, 154, and 203 from the stored designs."""
    matrices = json.loads(
        (ROOT / "data/spectrum/63_difference_matrices.json").read_text()
    )["matrices"]

    def gf4_mul(a, b):
        result = 0
        while b:
            if b & 1:
                result ^= a
            b >>= 1
            a <<= 1
            if a & 4:
                a ^= 7
        return result

    for h, m in [(3, 5), (7, 4), (7, 5)]:
        q, k = h * (m - 1), 7
        entry = matrices[str(q)]
        moduli = entry["group_moduli"]

        def decode(x):
            digits = []
            for modulus in moduli:
                digits.append(x % modulus)
                x //= modulus
            return digits

        def encode(digits):
            result, place = 0, 1
            for digit, modulus in zip(digits, moduli):
                result += digit * place
                place *= modulus
            return result

        lookup = {}
        for row_index, row in enumerate(entry["rows"]):
            for shift in range(q):
                delta = decode(shift)
                block = [
                    encode(
                        [
                            (a + b) % modulus
                            for a, b, modulus in zip(value, delta, moduli)
                        ]
                    )
                    for value in row
                ]
                block.append(row_index)
                for i, j in combinations(range(k), 2):
                    key = i, j, block[i], block[j]
                    assert key not in lookup
                    lookup[key] = block

        def h_op(x, y):
            return (y - x) % 3 if h == 3 else (2 * y - x) % 7

        def m_op(x, y):
            return 3 * (x + y) % 5 if m == 5 else x ^ gf4_mul(2, y)

        def op(x, y):
            if x < h and y < h:
                return h_op(x, y)
            if x < h or y < h or (x - h) // q == (y - h) // q:
                group = ((y if x < h else x) - h) // q
                a, b = (x, 0) if x < h else ((x - h) % q % h, (x - h) % q // h + 1)
                c, d = (y, 0) if y < h else ((y - h) % q % h, (y - h) % q // h + 1)
                e, f = h_op(a, c), m_op(b, d)
                return e if f == 0 else h + group * q + (f - 1) * h + e
            i, a = divmod(x - h, q)
            j, b = divmod(y - h, q)
            block = lookup[i, j, a, b] if i < j else lookup[j, i, b, a]
            group = (2 * j - i) % 7
            return h + group * q + block[group]

        n = k * q + h
        table = [[op(x, y) for y in range(n)] for x in range(n)]
        assert table[0][0] == 0
        assert all(0 <= value < n for row in table for value in row)
        for x in range(n):
            assert len(set(table[x])) == n
            assert len({table[y][x] for y in range(n)}) == n
            for y in range(n):
                assert table[y][table[x][table[x][y]]] == x


def main():
    path = ROOT / "data/spectrum/63_constructions.json"
    data = json.loads(path.read_text())
    extra_designs = check_difference_matrices()
    done, missing = check_certificate(data, extra_designs)
    check_order_41()
    check_singular_examples()
    print(
        f"Checked {len(done['idempotent'])} idempotent and "
        f"{len(done['pointed'])} pointed construction nodes."
    )
    print("Checked additional transversal designs:", sorted(extra_designs.items()))
    print(f"Finite starting range: {data['cutoff']}..{data['induction_start'] - 1}.")
    print(f"The documented induction constructs every order >= {data['cutoff']}.")
    print("Orders not constructed by the base certificate below the cutoff:", missing)
    print("Independently checked all 1681 law instances of the order-41 example.")
    print("Independently checked the full tables at orders 87, 154, and 203.")
    from spectrum_63_bennett import build
    from spectrum_63_atp import validate

    additional = build()
    manifest = json.loads(
        (ROOT / "data/spectrum/63_bennett_constructions.json").read_text()
    )
    extra_orders = set()
    for row in manifest["models"]:
        n = row["order"]
        q = additional[n]
        validate(q, n, 229)
        t = [[r.index(y) for y in range(n)] for r in q]
        validate(t, n)
        assert (
            hashlib.sha256(json.dumps(t, separators=(",", ":")).encode()).hexdigest()
            == row["e63_table_sha256"]
        )
        extra_orders.add(n)
    print("Additional independently reconstructed models:", sorted(extra_orders))
    print(
        "Remaining without a local model certificate, excluding known negative orders:",
        sorted(set(missing) - extra_orders - {2, 6, 10, 14}),
    )
    print(
        "Bennett also proves existence at 90; that construction is not yet replayed locally."
    )
    print("Research certificate only; no new Lean proof status is asserted.")


if __name__ == "__main__":
    main()
